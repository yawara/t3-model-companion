from pathlib import Path
import os, subprocess, tempfile
repo = Path('/home/ywr/t3-model-companion')
fixture = Path(tempfile.mkdtemp(prefix='t3-visibility-fixture-'))
(fixture / 'T3').mkdir()
lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=repo, text=True).strip()
lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=repo, text=True).strip()
env = os.environ.copy()
env['LEAN_PATH'] = str(fixture) + ':' + ':'.join(str((repo / p).resolve()) if not Path(p).is_absolute() else p for p in lean_path.split(':'))
(fixture / 'T3/Probe.lean').write_text('''module
public import Mathlib.Init
namespace Probe
theorem hiddenOrdinary : True := True.intro
public theorem publicGood : True := hiddenOrdinary
private theorem hiddenPrivate : True := True.intro
def hiddenDef : Nat := 42
public def publicDef : Nat := hiddenDef
end Probe
''')
(fixture / 'T3/Hidden.lean').write_text('module\npublic import Mathlib.Init\npublic theorem hiddenModulePublic : True := True.intro\n')
(fixture / 'T3.lean').write_text('module\npublic import T3.Probe\nimport T3.Hidden\n')
(fixture / 'Probe.lean').write_text('''module
import T3
public meta import Lean.Elab.Command
open Lean Elab Command
public meta section
run_cmd do
  let localEnv ← getEnv
  let privateEnv ← Lean.importModules #[{ module := `T3 }] {} (level := .private)
  let exportedEnv ← Lean.importModules #[{ module := `T3 }] {} (level := .exported)
  let nonpublicEnv ← Lean.importModules #[{ module := `T3, isExported := false }] {} (level := .exported)
  let names := privateEnv.constants.map₁.fold (init := #[]) fun names name _ =>
    if name.toString.contains "hidden" || name.toString.contains "publicGood" ||
        name.toString.contains "publicDef" then names.push name else names
  for name in names do
    if (privateEnv.getModuleIdxFor? name |>.map (privateEnv.header.moduleNames[·]!)) == some `T3.Probe || (privateEnv.getModuleIdxFor? name |>.map (privateEnv.header.moduleNames[·]!)) == some `T3.Hidden then
      logInfo m!"{name}: privateName={isPrivateName name}; local={localEnv.contains name}; localExporting={(localEnv.setExporting true).contains name}; private={privateEnv.contains name}; privateExporting={(privateEnv.setExporting true).contains name}; exported={exportedEnv.contains name}; exportedExporting={(exportedEnv.setExporting true).contains name}; nonpublic={nonpublicEnv.contains name}; nonpublicExporting={(nonpublicEnv.setExporting true).contains name}"
  logInfo m!"isModule private={privateEnv.header.isModule} exported={exportedEnv.header.isModule}"
''')
for source in ['T3/Probe', 'T3/Hidden', 'T3', 'Probe']:
    args = [lean, '-o', source + '.olean', source + '.lean']
    p = subprocess.run(args, cwd=fixture, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (fixture / (source.replace('/', '-') + '.log')).write_text(p.stdout)
    print(source, 'exit', p.returncode, p.stdout)
    if p.returncode:
        print('fixture', fixture)
        raise SystemExit(p.returncode)
print('fixture', fixture)
