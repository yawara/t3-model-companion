#!/usr/bin/env python3
"""Check local Palomar metadata consistency; this is not a Palomar approval.

Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0; see LICENSE.
Install the pinned Python dependencies with requirements-palomar.txt.
See palomar-schema/README.md for the scope and upstream input revisions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib

import yaml
from jsonschema.validators import validator_for


ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = Path(__file__).resolve().parent / "palomar-schema"
PINNED_INPUTS = {
    "v0.4.schema.json": "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce",
    "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "arxiv-codes.json": "aca149ce8d56144aebd1d12ff0bfbe67bd412f36b8401a88704635ff20c24911",
    "msc2020-codes.json": "711221fc1a61ac16efd153086836dc3e6debd256de0aef5b41616e75ea4b0333",
    "PALOMAR-LICENSE": "10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21",
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RESULTS = {
    "T3.exists_bounded_nonamalgamation_witness": (
        "main.bounded_witness", "T3.Main.BoundedWitness"),
    "T3.has_model_companion": ("main.model_companion", "T3.Main.ModelCompanion"),
}
LICENSE_NAME = re.compile(r"(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?", re.I)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique_pairs(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate mapping key: {key!r}")
        result[key] = value
    return result


class MetadataLoader(yaml.SafeLoader):
    """Accept ordinary YAML, without duplicate or merge keys."""


def unique_yaml_mapping(loader: MetadataLoader, node: yaml.MappingNode) -> dict:
    require(all(key.tag != "tag:yaml.org,2002:merge" for key, _ in node.value),
            "YAML merge keys are not accepted")
    return unique_pairs([(loader.construct_object(key), loader.construct_object(value))
                         for key, value in node.value])


MetadataLoader.add_constructor("tag:yaml.org,2002:map", unique_yaml_mapping)


def regular_file(root: Path, relative: str) -> Path:
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), f"path escapes repository: {relative}")
    require(path.is_file() and not path.is_symlink(), f"not a regular file: {relative}")
    return path


def nonempty_text(value: object, label: str, maximum: int | None = None) -> None:
    require(isinstance(value, str) and bool(value.strip()), f"{label} must be nonempty text")
    require(maximum is None or len(value) <= maximum, f"{label} exceeds {maximum} characters")


def distinct_strings(value: object, label: str, minimum: int, maximum: int) -> None:
    require(isinstance(value, list) and minimum <= len(value) <= maximum,
            f"{label} must contain {minimum}-{maximum} entries")
    for entry in value:
        nonempty_text(entry, label)
    require(len(value) == len(set(value)), f"{label} contains duplicates")


def check(root: Path) -> None:
    for name, expected in PINNED_INPUTS.items():
        require(hashlib.sha256((SCHEMAS / name).read_bytes()).hexdigest() == expected,
                f"pinned metadata input changed: {name}")
    source = regular_file(root, "formalization.yaml").read_bytes()
    require(len(source) <= 256 * 1024, "formalization.yaml exceeds 256 KiB")
    data = yaml.load(source.decode("utf-8"), Loader=MetadataLoader)
    schema = json.loads((SCHEMAS / "v0.4.schema.json").read_text())
    validator = validator_for(schema)
    validator.check_schema(schema)
    errors = list(validator(schema).iter_errors(data))
    require(not errors, "schema errors: " + "; ".join(
        f"{'.'.join(map(str, error.absolute_path))}: {error.message}" for error in errors))
    require(data.get("version") == "v0.4", "metadata must declare version: v0.4")
    require("repository" not in data, "this substantive development omits repository metadata")
    project = data["project"]
    nonempty_text(project["name"], "project.name", 300)
    nonempty_text(project.get("description"), "project.description", 10000)
    for field in ("authors", "responsible_maintainers"):
        distinct_strings(project.get(field), f"project.{field}", 1, 1000)
    require(project["license"] == "Apache-2.0", "this project declares Apache-2.0")
    license_files = [path for path in root.iterdir() if LICENSE_NAME.fullmatch(path.name)]
    require(len(license_files) == 1, "repository root must have exactly one conventional license")
    license_text = regular_file(root, license_files[0].name).read_bytes().replace(b"\r\n", b"\n")
    require(license_text == (SCHEMAS / "LICENSE").read_bytes(),
            "root license does not match the reviewed Apache-2.0 text")

    classification = data.get("classification", {})
    for field, minimum in (("arxiv", 1), ("msc2020", 0)):
        codes = classification.get(field, [])
        distinct_strings(codes, f"classification.{field}", minimum, 8)
        known = set(json.loads((SCHEMAS / f"{field}-codes.json").read_text()))
        require(set(codes) <= known, f"unrecognized {field} classification: {set(codes) - known}")
    for method in data["automation"]["methods"]:
        nonempty_text(method["method"], "automation.methods[].method")
    nonempty_text(data["review"]["status"], "review.status")
    sources = data["sources"]
    for item in sources:
        nonempty_text(item["title"], "sources[].title")
        require(item.get("relationship") in {
            "formalizes", "adapts", "independently-proves", "background", "other"},
            "sources[].relationship must use a standard category")
        require(item.get("type") != "original-proof", "this is a source-based formalization")
    require(any(item["relationship"] in {"formalizes", "adapts", "independently-proves"}
                for item in sources), "a substantive mathematical source is required")

    paper_map = tomllib.loads(regular_file(root, "docs/paper-map.toml").read_text())
    paper = paper_map["source"]
    paper_hash = hashlib.sha256(regular_file(root, paper["path"]).read_bytes()).hexdigest()
    require(paper_hash == paper["sha256"], "manuscript hash differs from the paper map")
    paper_sources = [item for item in sources if item.get("id") == paper["path"]]
    require(len(paper_sources) == 1 and paper_sources[0]["relationship"] == "formalizes",
            "metadata must formalize the paper-map source at its repository-relative path")
    require(paper_hash in paper_sources[0].get("note", ""), "source note omits manuscript SHA256")

    raw_config = regular_file(root, "comparator.json").read_bytes()
    require(len(raw_config) <= 1024 * 1024, "comparator.json exceeds 1 MiB")
    config = json.loads(raw_config, object_pairs_hook=unique_pairs)
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    require(isinstance(config, dict) and required <= config.keys()
            and config.keys() <= required | {"definition_names", "enable_nanoda"},
            "comparator.json has missing or unsupported keys")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "this project compares root Challenge and Solution modules")
    regular_file(root, "Challenge.lean")
    regular_file(root, "Solution.lean")
    distinct_strings(config["theorem_names"], "theorem_names", 2, 2)
    require(set(config["theorem_names"]) == set(RESULTS), "Comparator must select both main results")
    require(config.get("definition_names", []) == [], "this submission has no unspecified definitions")
    distinct_strings(config["permitted_axioms"], "permitted_axioms", 0, 3)
    require(set(config["permitted_axioms"]) <= AXIOMS, "Comparator permits a nonstandard axiom")
    require(config.get("enable_nanoda") is True, "local comparison must enable NanoDa")
    status = data.get("status", {})
    require(status.get("sorry_count") == 0 and status.get("sorry_in_definitions") == 0,
            "proof development must report zero holes; deliberate Challenge holes are excluded")
    require(set(status.get("axioms", [])) == AXIOMS, "status must record the three audited axioms")
    for field in ("scope",):
        nonempty_text(status.get(field), f"status.{field}")
    nonempty_text(data.get("fidelity", {}).get("divergences"), "fidelity.divergences")

    main_results = status.get("main_results", [])
    alignment = data.get("alignment", {}).get("statements", [])
    require(len(main_results) == 2 and {item.get("declaration") for item in main_results} == set(RESULTS),
            "status.main_results must match Comparator")
    require(len(alignment) == 2 and {item.get("lean") for item in alignment} == set(RESULTS),
            "alignment.statements must match Comparator")
    items_by_id = {item["id"]: item for item in paper_map["items"]}
    for name, (paper_id, module) in RESULTS.items():
        entry = items_by_id[paper_id]
        require(entry["formalization"] == "proved" and entry["fidelity"] == "proof_checked",
                f"paper map has not completed {paper_id}")
        require(any(binding["name"] == name and binding["module"] == module
                    and binding["kind"] == "theorem" for binding in entry["declarations"]),
                f"paper map does not bind {name} to {module}")
        result = next(item for item in main_results if item["declaration"] == name)
        expected_file = module.replace(".", "/") + ".lean"
        require(result.get("file") == expected_file and result.get("comparator_config") == "comparator.json",
                f"wrong file or Comparator path for {name}")
        regular_file(root, expected_file)
        aligned = next(item for item in alignment if item["lean"] == name)
        require(aligned.get("module") == module and aligned.get("status") == "proved",
                f"wrong alignment module or status for {name}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root to check")
    args = parser.parse_args()
    try:
        check(args.root.resolve())
    except (ValueError, TypeError, KeyError, OSError, yaml.YAMLError) as error:
        print(f"Palomar metadata check failed: {error}", file=sys.stderr)
        return 1
    print("Local Palomar metadata check passed; proof verification and Palomar review are separate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
