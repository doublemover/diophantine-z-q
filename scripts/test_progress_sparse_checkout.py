#!/usr/bin/env python3
"""Pure Git/source tests; no Lean, network, credentials or hosted mutation."""
import importlib.util,json,os,pathlib,shutil,subprocess,tempfile,unittest,textwrap
from unittest.mock import patch
import prepare_progress_sparse_checkout as s
class SparseCheckoutTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=pathlib.Path(self.tmp.name)
  self.g('init','-q');self.g('config','user.name','SourceTest');self.g('config','user.email','source-test@example.invalid')
  self.write('scripts/prepare_progress_sparse_checkout.py',pathlib.Path(s.__file__).read_text())
  self.write('.github/actions/example/action.yml','name: example\n')
  self.write('quartics/quartic-318-326/proof/progress/Base.lean','-- baseline preserved\n')
  self.write('lean/lean-toolchain','leanprover/lean4:v4.35.0\n')
  self.write('quartics/quartic-318-326/proof/progress/lean-toolchain','leanprover/lean4:v4.35.0\n')
  self.write(s.EXPERIMENTS+'/packets.json',{'active_packets':['test-r2']})
  self.write(s.EXPERIMENTS+'/test-r2/intake.json',{'revision_classification_schema':1,'revision_of':'test-r1'})
  self.write(s.EXPERIMENTS+'/test-r2/APPLICATION.json',{'predecessor':'test-r1','bindings':{'INHERITANCE.json':'bound-by-native-checker'}})
  self.write(s.EXPERIMENTS+'/test-r2/INHERITANCE.json',{'predecessor':'test-r1'})
  for name in ['test-r1','test-r2','irrelevant-r1']:
   if name!='test-r2':self.write(s.EXPERIMENTS+'/'+name+'/intake.json',{})
   self.write(s.EXPERIMENTS+'/'+name+'/Root.lean','-- exact source '+name+'\n')
   self.write(s.EXPERIMENTS+'/'+name+'/evidence/deep/report.txt','full evidence retained\n')
  self.commit()
 def tearDown(self):self.tmp.cleanup()
 def g(self,*a):return subprocess.check_output(['git','-C',str(self.root),*a],stderr=subprocess.PIPE).decode().strip()
 def write(self,p,v):
  q=self.root/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(v) if isinstance(v,dict) else v)
 def commit(self):self.g('add','.');self.g('commit','-qm','fixture');self.head=self.g('rev-parse','HEAD')
 def paths(self,name='test-r2'):return s.materialization_paths(self.root,name,self.head)
 def test_exact_paths(self):self.assertEqual(self.paths(),[s.EXPERIMENTS+'/test-r2',s.EXPERIMENTS+'/test-r1'])
 def test_inactive(self):
  with self.assertRaises(ValueError):self.paths('irrelevant-r1')
 def test_injection(self):
  for n in ['../bad','test-r2\n/','--help','test_r2','Test-r2','']:
   with self.assertRaises(ValueError):self.paths(n)
 def test_conflicting_predecessor(self):
  self.write(s.EXPERIMENTS+'/test-r2/APPLICATION.json',{'predecessor':'other-r1'});self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_missing_predecessor(self):
  self.write(s.EXPERIMENTS+'/test-r2/intake.json',{'revision_classification_schema':1});self.write(s.EXPERIMENTS+'/test-r2/APPLICATION.json',{});self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_self_predecessor(self):
  self.write(s.EXPERIMENTS+'/test-r2/intake.json',{'revision_classification_schema':1,'revision_of':'test-r2'});self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_wrong_schema(self):
  self.write(s.EXPERIMENTS+'/test-r2/intake.json',{'revision_classification_schema':True});self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_missing_prior_intake(self):
  (self.root/s.EXPERIMENTS/'test-r1/intake.json').unlink();self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_nonordinary_metadata(self):
  p=self.root/s.EXPERIMENTS/'test-r2/intake.json';p.unlink();p.symlink_to('../test-r1/intake.json');self.commit()
  with self.assertRaises(ValueError):self.paths()
 def test_legacy(self):
  self.write(s.EXPERIMENTS+'/test-r2/intake.json',{});self.commit();self.assertEqual(self.paths(),[s.EXPERIMENTS+'/test-r2'])
 def sparse(self):self.g('sparse-checkout','init','--cone');self.g('sparse-checkout','set','scripts','.github','lean','quartics/quartic-318-326/proof/progress')
 def command(self,*args,head=None):
  env=dict(os.environ,GITHUB_SHA=head or self.head)
  return subprocess.run(['python3','-B',str(self.root/'scripts/prepare_progress_sparse_checkout.py'),'--packet','test-r2',*args],capture_output=True,text=True,env=env)
 def test_real_materialization_preserves_all_selected_and_predecessor(self):
  self.sparse();self.assertFalse((self.root/s.EXPERIMENTS/'test-r2').exists());r=self.command();self.assertEqual(r.returncode,0,r.stderr)
  for name in ['test-r1','test-r2']:self.assertTrue((self.root/s.EXPERIMENTS/name/'evidence/deep/report.txt').is_file())
  self.assertFalse((self.root/s.EXPERIMENTS/'irrelevant-r1').exists());self.assertEqual(self.g('diff','HEAD'),'');self.assertEqual(self.g('diff','--cached','HEAD'),'')
 def test_dry_run_no_materialization(self):
  self.sparse();r=self.command('--dry-run');self.assertEqual(r.returncode,0,r.stderr);self.assertFalse((self.root/s.EXPERIMENTS/'test-r2').exists())
 def test_wrong_event_head(self):self.sparse();self.assertNotEqual(self.command(head='0'*40).returncode,0)
 def test_dirty_worktree_rejected(self):self.sparse();self.write('scripts/dirty.txt','untracked harmless');self.write('.github/actions/example/action.yml','changed');self.assertNotEqual(self.command().returncode,0)
 def test_full_checkout_not_silently_reconfigured(self):self.assertNotEqual(self.command().returncode,0)
 def test_compiler_setup_pin_files_materialized(self):
  self.sparse()
  for path in ['lean/lean-toolchain','quartics/quartic-318-326/proof/progress/lean-toolchain']:
   self.assertEqual((self.root/path).read_text(),'leanprover/lean4:v4.35.0\n')
  # Extract the actual composite preflight, never installer/toolchain steps.
  action=(pathlib.Path(__file__).resolve().parents[1]/'.github/actions/setup-pinned-lean/action.yml').read_text()
  shell=textwrap.dedent(action.split('      run: |\n',1)[1].split('    - id: installer',1)[0])
  self.assertIn('cat lean/lean-toolchain',shell)
  self.assertNotIn('setup_pinned_lean.sh',shell)
  env=dict(os.environ,RUNNER_OS='Linux',RUNNER_ARCH='X64',ImageOS='ubuntu24')
  self.assertEqual(subprocess.run(['bash','-c',shell],cwd=self.root,env=env).returncode,0)
 def test_old_sparse_selection_reproduces_missing_root_pin(self):
  self.g('sparse-checkout','init','--cone');self.g('sparse-checkout','set','scripts','.github','quartics/quartic-318-326/proof/progress')
  self.assertFalse((self.root/'lean/lean-toolchain').exists())
 def test_both_live_matrix_workflows_include_root_pin_directory(self):
  root=pathlib.Path(__file__).resolve().parents[1]
  for file,job in [('progress-experiments.yml','  first-check:'),('progress-inventory.yml','  inventory:')]:
   text=(root/'.github/workflows'/file).read_text().split(job,1)[1]
   block=text.split('sparse-checkout: |',1)[1].split('      - ',1)[0]
   self.assertIn('\n            lean\n',block)
if __name__=='__main__':unittest.main()
