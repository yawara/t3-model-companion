#!/usr/bin/env python3
"""Generate and check the paper correspondence map using Python's standard library.

This checks source coverage and lexical declaration locations, not Lean elaboration,
kernel proofs, or mathematical faithfulness. Those are separate project gates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "docs/paper-map.toml"
OUTPUT = ROOT / "docs/paper-map.md"
ENVIRONMENTS = {
    "theorem", "lemma", "proposition", "corollary", "definition", "example",
    "question", "conjecture", "fact", "remark", "notation",
}
FORMALIZATION = {"planned", "partial", "stated", "proved", "open"}
FIDELITY = {"unchecked", "statement_checked", "proof_checked"}
# Ordinary Lean identifiers include Unicode letters and subscripts, as in `map₂`.
NAME = r"[^\W\d][\w'.]*"


class MapError(ValueError):
    """An invalid source map or declaration binding."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise MapError(message)


def repo_path(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT), f"Path leaves the repository: {relative}")
    return path


def source_span(source: str, locator: dict, context: str) -> list[str]:
    """Validate a one-based inclusive locator before slicing a manuscript."""
    lines = source.splitlines()
    start, end = locator["line_start"], locator["line_end"]
    require(type(start) is int and type(end) is int and 1 <= start <= end <= len(lines),
            f"{context}: source locator outside manuscript")
    return lines[start - 1:end]


def uncomment_tex(source: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", source)


def active_tex(source: str) -> str:
    """Mask the manuscript's literal conditionals, preserving source positions.

    The archived v8 manuscript uses a false ``\\if0 ... \\fi`` block. Literal
    ``\\iffalse``/``\\iftrue`` and nesting are also supported. Other TeX
    conditionals need explicit support rather than guessed source coverage.
    """
    result = []
    stack: list[tuple[bool, bool, bool]] = []
    enabled = True
    position = 0
    for match in re.finditer(r"\\if0(?![0-9])|\\(?:if[a-zA-Z]*|else|fi)\b", source):
        chunk = source[position:match.start()]
        result.append(chunk if enabled else re.sub(r"[^\n]", " ", chunk))
        token = match.group(0)
        if token in {r"\if0", r"\iffalse", r"\iftrue"}:
            condition = token == r"\iftrue"
            stack.append((enabled, condition, False))
            enabled = enabled and condition
        elif token == r"\else":
            require(bool(stack), "Unmatched TeX else")
            parent, condition, seen_else = stack[-1]
            require(not seen_else, "Repeated TeX else")
            stack[-1] = (parent, condition, True)
            enabled = parent and not condition
        elif token == r"\fi":
            require(bool(stack), "Unmatched TeX fi")
            enabled = stack.pop()[0]
        else:
            raise MapError(f"Unsupported TeX conditional: {token}")
        result.append(" " * len(token))
        position = match.end()
    require(not stack, "Unclosed TeX conditional")
    result.append(source[position:])
    return "".join(result)


def source_items(source: str, *, include_inactive: bool = False) -> list[dict]:
    """Read the manuscript's shared theorem counter, excluding proof-local Claims."""
    source = uncomment_tex(source)
    if not include_inactive:
        source = active_tex(source)
    alternatives = "|".join(sorted(ENVIRONMENTS | {"customproposition"}))
    pattern = re.compile(
        r"\\section\{[^}]*\}|\\begin\{(" + alternatives + r")\}"
    )
    section = counter = 0
    result = []
    for match in pattern.finditer(source):
        if match.group(0).startswith("\\section"):
            section += 1
            counter = 0
            continue
        environment = match.group(1)
        end = source.find("\\end{" + environment + "}", match.end())
        require(end >= 0, f"Unclosed TeX environment: {environment}")
        end += len("\\end{" + environment + "}")
        body = source[match.start():end]
        if environment == "customproposition":
            title = re.match(r"\{([^}]+)\}", source[match.end():])
            require(title is not None, "customproposition requires a title")
            number = title.group(1)
        else:
            counter += 1
            number = f"{section}.{counter}"
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        require(len(labels) <= 1, f"Multiple labels in {environment} {number}")
        depth = 0
        part_lines = []
        for token in re.finditer(r"\\begin\{enumerate\}|\\end\{enumerate\}|\\item\b", body):
            if token.group(0).startswith("\\begin"):
                depth += 1
            elif token.group(0).startswith("\\end"):
                depth -= 1
            elif depth == 1:
                part_lines.append(source.count("\n", 0, match.start() + token.start()) + 1)
        result.append({
            "environment": environment,
            "number": number,
            "line_start": source.count("\n", 0, match.start()) + 1,
            "line_end": source.count("\n", 0, end) + 1,
            "tex_label": labels[0] if labels else "",
            "part_lines": part_lines,
        })
    return result


def lean_code(source: str) -> str:
    """Mask nested comments and strings while preserving source line numbers."""
    result = []
    position = depth = 0
    string = False
    while position < len(source):
        pair = source[position:position + 2]
        character = source[position]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                position += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                position += 2
            else:
                result.append("\n" if character == "\n" else " ")
                position += 1
        elif string:
            if character == "\\":
                result.append(" ")
                position += 1
                if position < len(source):
                    result.append("\n" if source[position] == "\n" else " ")
                    position += 1
            else:
                string = character != '"'
                result.append("\n" if character == "\n" else " ")
                position += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            position += 2
        elif pair == "--":
            end = source.find("\n", position)
            if end < 0:
                end = len(source)
            result.extend(" " * (end - position))
            position = end
        elif character == '"':
            string = True
            result.append(" ")
            position += 1
        else:
            result.append(character)
            position += 1
    require(depth == 0 and not string, "Unclosed comment or string in Lean source")
    return "".join(result)


def declarations_in(path: Path) -> dict[str, tuple[str, int, bool]]:
    """Locate ordinary named declarations; exotic commands need explicit support."""
    stack: list[str | None] = []
    result = {}
    for number, raw_line in enumerate(lean_code(path.read_text()).splitlines(), 1):
        line = re.sub(r"^\s*@\[[^\]]*\]\s*", "", raw_line).strip()
        namespace = re.match(r"namespace\s+(" + NAME + r")\s*$", line)
        if namespace:
            stack.append(namespace.group(1))
            continue
        if re.match(r"(?:(?:public|noncomputable)\s+)*section(?:\s+" + NAME + r")?\s*$", line):
            stack.append(None)
            continue
        if re.match(r"end(?:\s+" + NAME + r")?\s*$", line):
            if stack:
                stack.pop()
            continue
        match = re.match(
            r"((?:(?:private|protected|noncomputable|public|unsafe)\s+)*)"
            r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\s+(" + NAME + r")",
            line,
        )
        if not match:
            continue
        modifiers, kind, name = match.groups()
        if name.startswith("_root_."):
            name = name.removeprefix("_root_.")
        else:
            name = ".".join([part for part in stack if part] + [name])
        require(name not in result, f"Ambiguous lexical declaration {name} in {path}")
        result[name] = (kind, number, "private" in modifiers.split())
    return result


def check_progress(entry: dict, context: str, modules: list[str], cache: dict,
                   manifest: dict | None = None) -> None:
    state = entry["formalization"]
    fidelity = entry["fidelity"]
    require(state in FORMALIZATION, f"{context}: invalid formalization {state}")
    require(fidelity in FIDELITY, f"{context}: invalid fidelity {fidelity}")
    plans = entry["planned_declarations"]
    bindings = entry["declarations"]
    require(isinstance(plans, list) and all(isinstance(name, str) for name in plans),
            f"{context}: planned_declarations must be a string list")
    require(isinstance(bindings, list), f"{context}: declarations must be a binding list")
    require(len(plans) == len(set(plans)), f"{context}: duplicate planned declaration")
    for binding in bindings:
        name, module = binding["name"], binding["module"]
        require(module in modules, f"{context}: binding module {module} is not registered")
        path = repo_path(module.replace(".", "/") + ".lean")
        require(path.is_file(), f"{context}: missing module {module}")
        if module not in cache:
            cache[module] = declarations_in(path)
        require(name in cache[module], f"{context}: declaration {name} not found in {module}")
        kind, line, private = cache[module][name]
        require(not private, f"{context}: {name} is private, not a public paper API")
        require(binding["kind"] == kind and binding["line"] == line,
                f"{context}: {name} is {kind} at line {line}; update its locator")
        if manifest is not None:
            checked = manifest.get(name)
            require(checked is not None, f"{context}: {name} absent from kernel declaration manifest")
            require(checked["module"] == module and not checked["private"],
                    f"{context}: kernel manifest module/private mismatch for {name}")
            require(checked["exported"], f"{context}: {name} is not exported through T3")
            require(set(checked["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"},
                    f"{context}: nonstandard axioms in kernel manifest for {name}")
    parts = entry.get("parts", [])
    actual = bool(bindings) or any(part["declarations"] for part in parts)
    require(state not in {"planned", "open"} or not actual,
            f"{context}: actual bindings require a progress state")
    require(state != "open" or (not plans and not parts and fidelity != "proof_checked"),
            f"{context}: an open question or conjecture has no claimed proof or implementation plan")
    require(state in {"planned", "open"} or actual, f"{context}: {state} requires actual declarations")
    if state in {"stated", "proved"}:
        require(all(part["formalization"] in {"stated", "proved"} for part in parts),
                f"{context}: incomplete parts require formalization='partial'")
    if state == "proved":
        require(all(part["formalization"] == "proved" for part in parts),
                f"{context}: proved requires every part proved")
        verification = entry.get("verification", {})
        require(bool(verification.get("code_revision")), f"{context}: proved needs a code revision")
        record = verification.get("record", "")
        require(bool(record) and repo_path(record).is_file(), f"{context}: proved needs a verification record")
    if fidelity == "statement_checked":
        require(all(part["fidelity"] != "unchecked" for part in parts),
                f"{context}: statement_checked requires every part checked")
    if fidelity == "proof_checked":
        require(state == "proved", f"{context}: proof_checked requires proved")
        require(all(part["fidelity"] == "proof_checked" for part in parts),
                f"{context}: proof_checked requires every part proof_checked")
    part_ids = [part["id"] for part in parts]
    require(len(part_ids) == len(set(part_ids)), f"{context}: duplicate part ID")
    for part in parts:
        check_progress(part, context + "." + part["id"], modules, cache, manifest)


def validate(data: dict, manifest: dict | None = None) -> None:
    require(data["schema_version"] == 1, "Unsupported paper-map schema")
    source = data["source"]
    path = repo_path(source["path"])
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    require(digest == source["sha256"], "TeX SHA256 changed; review and repin the source map")
    tex = path.read_text()
    active_source_lines = active_tex(uncomment_tex(tex)).splitlines()
    archived_sources = {}
    for archived in data.get("archived_sources", []):
        archived_path = archived["path"]
        require(archived_path != source["path"] and archived_path not in archived_sources,
                f"Duplicate source path: {archived_path}")
        archived_file = repo_path(archived_path)
        require(hashlib.sha256(archived_file.read_bytes()).hexdigest() == archived["sha256"],
                f"Archived TeX SHA256 changed: {archived_path}")
        archived_sources[archived_path] = archived_file.read_text()
    scanned = source_items(tex)
    active_lines = {item["line_start"] for item in scanned}
    inactive_scanned = [item for item in source_items(tex, include_inactive=True)
                        if item["line_start"] not in active_lines]
    numbered = [item for item in scanned if item["environment"] != "customproposition"]
    custom = [item for item in scanned if item["environment"] == "customproposition"]
    require(len(numbered) == source["numbered_items"] == 54, "Expected all 54 active numbered v9 items")
    require(len(custom) == source["custom_items"] == 1, "Expected Proposition A")
    items = data["items"]
    ids = [item["id"] for item in items]
    require(len(ids) == len(set(ids)), "Duplicate paper ID")
    active = [item for item in items if item.get("source_status", "active") == "active"]
    inactive = [item for item in items if item.get("source_status") == "inactive"]
    require(len(active) + len(inactive) == len(items), "Invalid source_status")
    require(source["unnumbered_items"] == 2 and len(active) == len(scanned) + 2,
            "Expected 54 active numbered items, Proposition A, and two unnumbered items")
    require(len(inactive_scanned) == source["inactive_numbered_items"] == 0
            and source["inactive_unnumbered_items"] == 0 and len(inactive) == 3,
            "Expected no disabled v9 items and three retained archived items")
    archived_scanned = []
    for item in inactive:
        source_path = item.get("source_path")
        require(source_path in archived_sources, f"{item['id']}: missing archived source")
        require(source_path == "archives/T3_modelcompanion_v8.tex",
                f"{item['id']}: retained item must use archived v8 source")
        if item["environment"] != "prose":
            matches = [entry for entry in source_items(archived_sources[source_path],
                                                       include_inactive=True)
                       if (entry["environment"], entry["number"]) ==
                       (item["environment"], item["number"])]
            require(len(matches) == 1, f"{item['id']}: archived source item missing or ambiguous")
            archived_scanned.extend(matches)
    require(len(archived_scanned) == 2, "Expected both archived questions")
    by_location = {(item["environment"], item["number"]): item for item in items}
    require(len(by_location) == len(items), "Duplicate source item")
    for item, expected_status in ([(entry, "active") for entry in scanned]
                                  + [(entry, "inactive") for entry in archived_scanned]):
        key = item["environment"], item["number"]
        require(key in by_location, f"Unregistered TeX item: {key}")
        registered = by_location[key]
        require(bool(registered.get("source_path")) == (expected_status == "inactive"),
                f"{registered['id']}: incorrect source path")
        require(registered.get("source_status", "active") == expected_status,
                f"{registered['id']}: incorrect source_status")
        for field in ("line_start", "line_end", "tex_label"):
            require(registered[field] == item[field], f"{registered['id']}: incorrect {field}")
        part_lines = [part["source_line"] for part in registered.get("parts", [])
                      if part.get("source_kind", "enumerated") == "enumerated"]
        require(part_lines == item["part_lines"], f"{registered['id']}: top-level enumerated part coverage differs")
        for part in registered.get("parts", []):
            require(part.get("source_kind", "enumerated") in {"enumerated", "clause"}
                    and item["line_start"] <= part["source_line"] <= item["line_end"],
                    f"{registered['id']}: invalid part source locator")
    exponent = next((item for item in items if item["id"] == "preliminaries.exponent_three"), None)
    require(exponent is not None, "Missing separate exponent-three convention")
    exponent_lines = source_span(tex, exponent, exponent["id"])
    require(exponent["environment"] == "prose" and exponent["number"] == "2.preamble"
            and exponent["line_end"] - exponent["line_start"] == 6
            and "Throughout, groups" in exponent_lines[0]
            and exponent["tex_label"] == "" and "T3.GroupTheory.Basic" in exponent["modules"],
            "Incorrect exponent-three convention locator or module")
    set_commutator = next((item for item in items if item["id"] == "preliminaries.set_commutator"), None)
    require(set_commutator is not None, "Missing separate set commutator definition")
    commutator_lines = source_span(tex, set_commutator, set_commutator["id"])
    require(set_commutator["environment"] == "prose"
            and set_commutator["number"] == "2.group_preamble"
            and set_commutator["line_end"] - set_commutator["line_start"] == 1
            and "For subsets" in commutator_lines[0]
            and set_commutator["tex_label"] == ""
            and set_commutator["modules"] == ["T3.GroupTheory.Basic"],
            "Incorrect set commutator definition locator or module")
    burnside = next((item for item in inactive if item["id"] == "questions.burnside_local_finiteness"), None)
    require(burnside is not None and burnside["environment"] == "prose"
            and burnside["number"] == "6.burnside_local_finiteness"
            and burnside["line_start"] == 1524 and burnside["line_end"] == 1530
            and burnside["tex_label"] == "",
            "Incorrect inactive Burnside reduction locator")
    takeuchi = next(item for item in items if item["id"] == "questions.takeuchi_conjecture")
    require(takeuchi["environment"] == "conjecture" and takeuchi["number"] == "1.1"
            and takeuchi["tex_label"] == "conj:burnside-model-companion",
            "Takeuchi conjecture must track active v9 Conjecture 1.1")
    require(takeuchi.get("additional_source_locations") == [{
        "source_path": "archives/T3_modelcompanion_v8.tex",
        "line_start": 1532, "line_end": 1535, "source_status": "inactive",
        "description": "Inactive Further questions: finite-rank Burnside groups formulation",
    }], "Takeuchi conjecture must retain its inactive Burnside formulation")
    for item_id in ["questions.locally_finite_varieties", "questions.bounded_exponent_varieties",
                    "questions.takeuchi_conjecture"]:
        item = next((entry for entry in items if entry["id"] == item_id), None)
        require(item is not None and item["formalization"] == "open",
                f"The manuscript leaves this question or conjecture open: {item_id}")
    identities = next((item for item in items if item["id"] == "preliminaries.elementary_identities"), None)
    require(identities is not None and identities["environment"] == "fact"
            and identities["number"] == "2.15"
            and "T3.GroupTheory.Identities" in identities["modules"],
            "Incorrect elementary-identities entry")
    require(items == active + inactive, "Archived items must follow the active manuscript")
    for group in [active, inactive]:
        require([item["line_start"] for item in group] == sorted(item["line_start"] for item in group),
                "Items must be in paper order within each source")
    cache = {}
    for item in items:
        context = item["id"]
        require(re.fullmatch(r"[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)+", context) is not None,
                f"Invalid stable paper ID: {context}")
        require(bool(item["title"]) and (bool(item["modules"]) or item["formalization"] == "open"),
                f"{context}: missing title or modules")
        for locator in [item] + item.get("additional_source_locations", []):
            source_path = locator.get("source_path", source["path"])
            require(source_path == source["path"] or source_path in archived_sources,
                    f"{context}: unregistered source path")
            archived = source_path in archived_sources
            source_text = archived_sources[source_path] if archived else tex
            require(any(line.strip() for line in
                        source_span(uncomment_tex(source_text), locator, context)),
                    f"{context}: empty source locator")
            if archived:
                require(locator.get("source_status") == "inactive",
                        f"{context}: archived source cannot be an active manuscript item")
            selected_lines = (active_tex(uncomment_tex(source_text)).splitlines()
                              if archived else active_source_lines)[locator["line_start"] - 1:locator["line_end"]]
            is_active = any(line.strip() for line in selected_lines)
            require(is_active == (locator.get("source_status", "active") == "active"),
                    f"{context}: source locator does not match active TeX")
        for module in item["modules"]:
            require(re.fullmatch(r"T3(?:\.[A-Z][A-Za-z0-9]*)+", module) is not None,
                    f"{context}: invalid module {module}")
            if item["formalization"] in {"stated", "proved"}:
                require(repo_path(module.replace(".", "/") + ".lean").is_file(),
                        f"{context}: missing module {module}")
        check_progress(item, context, item["modules"], cache, manifest)


def cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def declaration_link(binding: dict) -> str:
    path = binding["module"].replace(".", "/") + ".lean"
    return f"[{binding['name']}](../{path}#L{binding['line']})"


def render(data: dict) -> str:
    source = data["source"]
    items = data["items"]
    active = [item for item in items if item.get("source_status", "active") == "active"]
    inactive = [item for item in items if item.get("source_status") == "inactive"]
    counts = Counter(item["formalization"] for item in active)
    inactive_counts = Counter(item["formalization"] for item in inactive)
    lines = [
        "# 論文と Lean の対応表", "",
        "このファイルは `docs/paper-map.toml` から生成する。変更後は "
        "`python3 scripts/paper_map.py --write`、整合性検査は `--check` を使う。", "",
        f"対象: [{source['path']}](../{source['path']})。SHA256: `{source['sha256']}`。", "",
        "v9 の有効な本文は番号付き 54 項目（Conjecture 1.1 を含む）、Proposition A、"
        "§2 の無番号定義 2 項目の計 57 項目を登録する。"
        "アーカイブ v8 の旧 §6 から Questions 6.1–6.2 と Burnside 群による還元の"
        "3 項目を `inactive` として保持し、PDF 本文の項目数には含めない。"
        "行・表示番号は補助情報で、安定 ID を主キーとする。", "",
        "有効な本文の状態: " + ", ".join(f"`{state}` {counts[state]}" for state in
                                       ("planned", "partial", "stated", "proved", "open")) + "。", "",
        "非表示の保持項目: " + ", ".join(f"`{state}` {inactive_counts[state]}" for state in
                                           ("proved", "open")) + "。", "",
        "v8 からの出典差分と今回の照合の範囲は [v9 移行・レビュー記録](../notes/v9-migration.md) を参照する。"
        "既存の `verification` と `proof_checked` は過去の検証・照合記録を保持しており、"
        "今回の再照合・Lean の再検証とは区別する。", "",
        "`formalization` と `fidelity` は別々に記録する。`partial` は項目の一部だけに"
        "実在宣言がある状態、`stated` は型・定義の記述まで、`proved` は別の検証記録を"
        "伴う完成状態を表す。`unchecked` / `statement_checked` / `proof_checked` は"
        "原稿との照合状況である。`open` は原稿の未解決の質問・予想であり、"
        "証明済み結果や今回の実装予定を意味しない。", "",
        "このスクリプトは TeX の網羅性、モジュールと宣言の字句上の所在、表示の整合性を"
        "検査する。Lean の elaboration・公理依存・lint・数学的 faithful 性は別途検証する。"
        "予定名は実在宣言ではなく、未着手の項目のために Lean stub を作らない。", "",
        "| 論文項目 / 安定 ID | 内容 | 原文 label / 行 | source_status | 公開モジュール（予定を含む） | formalization | fidelity |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for item in items:
        label = f"`{item['tex_label']}`" if item["tex_label"] else "label なし"
        source_path = item.get("source_path", source["path"])
        locator = (f"{label}<br>[{source_path}](../{source_path}#L{item['line_start']})"
                   f"<br>{item['line_start']}–{item['line_end']}")
        modules = "<br>".join(f"`{module}`" for module in item["modules"]) or "—"
        if item["environment"] == "prose":
            name = {
                "2.preamble": "§2 冒頭",
                "2.group_preamble": "§2 群論の無番号定義",
                "6.burnside_local_finiteness": "§6 Burnside 群による還元",
            }[item["number"]]
        else:
            name = item["environment"].replace("customproposition", "proposition").title() + " " + item["number"]
        lines.append("| " + " | ".join(map(cell, [f"{name}<br>`{item['id']}`", item["title"],
                     locator, item.get("source_status", "active"), modules,
                     item["formalization"], item["fidelity"]])) + " |")
    lines.extend(["", "## 宣言と項目内の進捗", ""])
    for item in items:
        lines.extend([f"### `{item['id']}`", ""])
        if item.get("source_status") == "inactive":
            lines.extend([f"出典状態: `inactive`（[{item['source_path']}](../{item['source_path']})"
                          " の旧 §6。現行 v9 本文には含まれない）。", ""])
        planned = ", ".join(f"`{name}`" for name in item["planned_declarations"]) or "型の設計時に決める"
        actual = ", ".join(declaration_link(binding) for binding in item["declarations"]) or "なし"
        lines.extend([f"予定宣言: {planned}。", "", f"実在宣言: {actual}。", ""])
        if item.get("notes"):
            lines.extend([item["notes"], ""])
        for locator in item.get("additional_source_locations", []):
            source_path = locator.get("source_path", source["path"])
            lines.extend([f"追加出典: {locator['description']}、"
                          f"[{source_path}](../{source_path}#L{locator['line_start']})、"
                          f"{locator['line_start']}–{locator['line_end']} 行"
                          f"（`{locator.get('source_status', 'active')}`）。", ""])
        if item.get("parts"):
            lines.extend(["| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |",
                          "| --- | --- | --- | --- | --- |"])
            for part in item["parts"]:
                actual = ", ".join(declaration_link(binding) for binding in part["declarations"]) or "なし"
                lines.append("| " + " | ".join(map(cell, [part["id"],
                             f"{part['summary']} / {part['source_line']}", part["formalization"],
                             part["fidelity"], actual])) + " |")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check", action="store_true", help="validate source, bindings, and generated Markdown")
    modes.add_argument("--write", action="store_true", help="validate and regenerate Markdown")
    parser.add_argument("--declarations-json", type=Path,
                        help="also compare actual bindings with Tests/Axioms.lean kernel manifest")
    args = parser.parse_args()
    try:
        data = tomllib.loads(MAP.read_text())
        manifest = None
        if args.declarations_json:
            exported = json.loads(args.declarations_json.read_text())
            declarations = exported["declarations"]
            manifest = {declaration["name"]: declaration for declaration in declarations}
            require(len(manifest) == len(declarations), "Duplicate declaration in kernel manifest")
        validate(data, manifest)
        expected = render(data)
        if args.write:
            OUTPUT.write_text(expected)
            print(f"Generated {OUTPUT.relative_to(ROOT)} ({len(data['items'])} items).")
        else:
            require(OUTPUT.is_file() and OUTPUT.read_text() == expected,
                    "Generated Markdown differs; run python3 scripts/paper_map.py --write")
            print("Paper map OK: 54 active numbered items + Proposition A + 2 unnumbered items; "
                  "3 inactive items retained; source and bindings checked.")
            if manifest is not None:
                print("Actual bindings also matched the supplied kernel declaration manifest.")
        return 0
    except (MapError, OSError, KeyError, TypeError, tomllib.TOMLDecodeError, json.JSONDecodeError) as error:
        print(f"paper-map: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
