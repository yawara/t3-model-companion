from pathlib import Path
import os,shutil,subprocess,tempfile,json
repo=Path('/home/ywr/t3-model-companion')
fixture=Path(tempfile.mkdtemp(prefix='t3-audit-fixture-'))
(fixture/'T3').mkdir();(fixture/'Tests').mkdir()
lean_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
lean=subprocess.check_output(['lake','env','which','lean'],cwd=repo,text=True).strip()
env=os.environ.copy()
env['LEAN_PATH']=str(fixture)+':'+':'.join(str((repo/p).resolve()) if not Path(p).is_absolute() else p for p in lean_path.split(':'))
env['T3_DECLARATIONS_JSON']=str(fixture/'declarations.json')
(fixture/'T3.lean').write_text('module\npublic import T3.Probe\n')
base='module\npublic import Mathlib.Init\nprivate theorem hiddenGood : True := True.intro\nnamespace Nat\npublic theorem auditFixtureGood : True := True.intro\nend Nat\n'
shutil.copyfile(repo/'Tests/Axioms.lean',fixture/'Tests/Axioms.lean')
(fixture/'T3/Probe.lean').write_text(base)
def run(args,label):
 p=subprocess.run([lean,*args],cwd=fixture,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (fixture/(label+'.log')).write_text(p.stdout)
 print(label,'exit',p.returncode,p.stdout[:6000])
 return p.returncode
for mod in ['T3/Probe','T3']:
 if run(['-o',mod+'.olean',mod+'.lean'],'build-'+mod.replace('/','-')): raise SystemExit(1)
rc=run(['-DautoImplicit=false','-Dlinter.mathlibStandardSet=true','-Dlinter.style.header=true','-Dlinter.style.longFile=1500','-DwarningAsError=true','Tests/Axioms.lean'],'positive')
print('fixture',fixture)
if rc: raise SystemExit(1)
d=json.loads((fixture/'declarations.json').read_text())
assert any(x['private'] and 'hiddenGood' in x['name'] for x in d['declarations'])
assert any(x['name']=='Nat.auditFixtureGood' for x in d['declarations'])
(fixture/'T3/Probe.lean').write_text(base+'private axiom hiddenBad : False\n')
for mod in ['T3/Probe','T3']:
 if run(['-o',mod+'.olean',mod+'.lean'],'negative-build-'+mod.replace('/','-')): raise SystemExit(1)
assert run(['Tests/Axioms.lean'],'negative-private')!=0
assert 'hiddenBad' in (fixture/'negative-private.log').read_text()
(fixture/'T3/Probe.lean').write_text(base+'namespace Nat\npublic axiom auditFixtureBad : False\nend Nat\n')
for mod in ['T3/Probe','T3']:
 if run(['-o',mod+'.olean',mod+'.lean'],'standard-build-'+mod.replace('/','-')): raise SystemExit(1)
assert run(['Tests/Axioms.lean'],'negative-standard')!=0
assert 'Nat.auditFixtureBad' in (fixture/'negative-standard.log').read_text()
print('all controls passed')
