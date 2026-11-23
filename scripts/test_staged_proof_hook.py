"""Staged standalone lint tests. Real Lean tests require QUARTIC_LEAN."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import check_staged_lean as lint

SCRIPT = Path(lint.__file__)
TOOL = 'leanprover/lean4:v4.35.0\n'
A = b'import Lean\n def stagedNat : Nat := 5\n'
B = b'import StageA\n theorem stagedFive : stagedNat = 5 := rfl\n'
BROKEN = b'import StageA\n theorem stagedFive : stagedNat = 6 := rfl\n'
TYPECLASS = '''
section
variable {a : Type} [inst : Inhabited a]
include inst in
theorem lintExample (x : a) : x = x := rfl
end
'''.encode()
TYPECLASS_USED = b'''
section
variable {a : Type} [inst : Inhabited a]
theorem lintExample : (default : a) = default := rfl
end
'''
LEAN = os.getenv('QUARTIC_LEAN')
EXACT_ROOT = Path(os.getenv('QUARTIC_TEST_LOCK_ROOT',SCRIPT.parents[1]))
HAVE_EXACT_LOCKS = all((EXACT_ROOT/p).is_file() for p in lint.LOCKS)


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='staged-lean-fixture-')
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)/'repo'
        self.repo.mkdir()
        self.cache = Path(self.tmp.name)/'cache'
        self.git('init','-q')
        self.git('config','user.email','fixture@example.invalid')
        self.git('config','user.name','Fixture')
        self.git('config','core.hooksPath',str(self.repo/'no-hooks'))
        self.git('config','core.autocrlf','false')
        self.write('README.md',b'baseline\n')
        # The source pins are independently tested against the original tree;
        # tests receive an exact projection with no complete project checkout.
        for p in lint.LOCKS:
            self.write(p, (EXACT_ROOT/p).read_bytes() if HAVE_EXACT_LOCKS else TOOL.encode())
        self.git('add','.')
        self.git('commit','-qm','base')

    def git(self,*args):
        return subprocess.check_output(['git','-C',str(self.repo),*args],stderr=subprocess.STDOUT)

    def write(self,path,raw):
        path=self.repo/path
        path.parent.mkdir(exist_ok=True,parents=True)
        path.write_bytes(raw)

    def packet(self,a=A,b=B, *, stage=True, manifest_order=None, dependencies=None):
        root = lint.INTAKE + 'bench/'
        paths = {'StageA':a,'StageB':b}
        for n, content in paths.items():
            self.write(root+n+'.lean',content)
        dep = dependencies or {'StageA':['Lean'],'StageB':['StageA']}
        self.write(root+'intake.json', lint.json_bytes(dict(order=manifest_order or list(paths),
            files={n+'.lean':dict(sha256=lint.digest(v),imports=dep[n]) for n,v in paths.items()})))
        if stage:
            self.git('add',root)
        return root

    def call(self, *opts, lean=LEAN):
        cmd=[sys.executable,'-I','-B',str(SCRIPT), '--cache',str(self.cache),*opts]
        if lean:
            cmd += ['--lean',str(lean)]
        env={k:v for k,v in os.environ.items() if not k.startswith('QUARTIC_LEAN')}
        p=subprocess.run(cmd,cwd=self.repo,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        return p.returncode,json.loads(p.stdout),p.stderr

    def has_pin(self):
        if not HAVE_EXACT_LOCKS:
            self.skipTest('set QUARTIC_TEST_LOCK_ROOT to exact project lock projection')

    def actual(self):
        self.has_pin()
        if not LEAN:
            self.skipTest('native measure requires official QUARTIC_LEAN binary')

    def test_nonlean_is_na(self):
        self.write('README.md',b'change\n'); self.git('add','README.md')
        code,data,_=self.call(lean=None)
        self.assertEqual((code,data['status']),(0,'N/A'))

    def test_staged_pin_blocks_before_compiler(self):
        self.write('lean/lean-toolchain',b'changed\n'); self.git('add','lean/lean-toolchain')
        code,data,_=self.call(lean=None)
        self.assertEqual((code,data['status']),(2,'NOT RUN / BLOCKED'))
        self.assertIn('staged toolchain',data['diagnostic'])

    def test_unreachable_dependency_order_blocks(self):
        self.has_pin()
        self.packet(manifest_order=['StageB','StageA'])
        code,data,_=self.call(lean=None)
        self.assertEqual(code,2); self.assertIn('nonpreceding',data['diagnostic'])

    def test_missing_compiler_never_passes(self):
        self.has_pin()
        self.packet()
        code,data,_=self.call(lean=None)
        self.assertEqual(code,2); self.assertIn('official Lean binary',data['diagnostic'])

    def test_source_cannot_switch_off_lint(self):
        self.has_pin()
        self.packet(b=B+b'\nset_option linter.unusedSectionVars false\n')
        code,data,_=self.call(lean=None)
        self.assertEqual(code,2); self.assertIn('overrides',data['diagnostic'])

    def test_real_unused_instance_and_stage_vs_worktree(self):
        self.actual()
        base=self.packet(b=B+TYPECLASS)
        self.write(base+'StageB.lean',B+TYPECLASS_USED)  # Unstaged pass must not mask staged diagnostic.
        code,data,diagnostics=self.call()
        self.assertEqual((code,data['status']),(1,'FAIL'),diagnostics)
        self.assertIn('"kind":"linter.unusedSectionVars"',diagnostics)
        self.assertIn(base+'StageB.lean',diagnostics)
        self.packet(b=B+TYPECLASS_USED)
        code,data,diagnostics=self.call()
        self.assertEqual((code,data['status']),(0,'PASS'),diagnostics)

    def test_real_cold_warm_dependency_and_source_change(self):
        self.actual()
        self.packet()
        self.git('commit','-qm','seed')
        self.packet(b=B+b'\n-- staged revision\n')
        c,d,e=self.call(); self.assertEqual((c,d['elaborated'],d['reused']),(0,['StageA','StageB'],[]),e)
        c,d,e=self.call(); self.assertEqual((c,d['elaborated'],d['reused']),(0,['StageB'],['StageA']),e)
        self.git('commit','-qm','unrelated-to-A')
        self.packet(b=B+b'\n-- another staged revision\n')
        c,d,e=self.call(); self.assertEqual((c,d['elaborated'],d['reused']),(0,['StageB'],['StageA']),e)
        self.packet(a=A.replace(b'5',b'6'))
        c,d,e=self.call(); self.assertEqual((c,d['status'],d['reused']),(1,'FAIL',[]),e)

    def test_real_corrupt_dependency_cache_and_missing_upstream(self):
        self.actual()
        self.packet()
        self.git('commit','-qm','seed')
        self.packet(b=B+b'\n-- staged revision\n')
        c,d,e=self.call(); self.assertEqual(c,0,e)
        entry=next(self.cache.glob('*/StageA.olean'))
        entry.write_bytes(b'not an olean')
        c,d,e=self.call(); self.assertEqual(c,2,e); self.assertIn('corrupt dependency',e)
        self.packet(a=A.replace(b'import Lean',b'import Mathlib'),
                    dependencies={'StageA':['Mathlib'],'StageB':['StageA']})
        c,d,e=self.call(); self.assertEqual(c,2,e); self.assertIn('pinned upstream imports missing',e)

    def test_immutable_external_donor_reads_staging(self):
        self.actual()
        donor = lint.PROGRESS + 'StageA.lean'
        self.write(donor,A)
        self.git('add',donor); self.git('commit','-qm','saved donor')
        root = self.packet(stage=False)
        (self.repo/(root+'StageA.lean')).unlink()
        self.git('add',root)
        context='docs/ci-example/CONTRACT.json'
        self.write(context,lint.json_bytes({'rows':{'bench':{
            'manifest_sha256':lint.digest((self.repo/(root+'intake.json')).read_bytes()),
            'source_paths':{'StageA':donor}}}}))
        self.git('add',context)
        self.write(donor,A.replace(b'5',b'6'))  # Must not change the immutable index donor.
        c,d,e=self.call(); self.assertEqual((c,d['elaborated']),(0,['StageA','StageB']),e)

    def test_real_module_mode_reuses_ir_signature_companion(self):
        self.actual()
        a = b"""module
public meta import Lean.Elab.Command
import Lean.Elab.Command
public section
@[expose] def stagedNat : Nat := 5
"""
        b = b"""module
public import StageA
public meta import StageA
public section
theorem stagedFive : stagedNat = 5 := rfl
"""
        deps={'StageA':['Lean.Elab.Command'],'StageB':['StageA']}
        self.packet(a=a,b=b,dependencies=deps); self.git('commit','-qm','seed module mode')
        self.packet(a=a,b=b+b'-- changed staged leaf\n',dependencies=deps)
        c,r,e=self.call(); self.assertEqual((c,r['elaborated']),(0,['StageA','StageB']),e)
        sig=next(self.cache.glob('*/StageA.ir.sig'))
        self.assertGreater(sig.stat().st_size,0)
        c,r,e=self.call(); self.assertEqual((c,r['elaborated'],r['reused']),(0,['StageB'],['StageA']),e)
        sig.unlink()
        c,r,e=self.call(); self.assertEqual(c,2,e); self.assertIn('cache contents',e)

    def test_staged_ci_contract_manifest_drift_blocks(self):
        self.has_pin()
        self.packet()
        path='docs/ci-drift/CONTRACT.json'
        self.write(path,lint.json_bytes({'rows':{'bench':{
            'manifest_sha256':'0'*64, 'source_paths':{}}}}))
        self.git('add',path)
        code,data,_=self.call(lean=None)
        self.assertEqual(code,2); self.assertIn('manifest differs',data['diagnostic'])

    def test_cold_artifact_reused_by_independent_git_index(self):
        self.actual()
        self.packet(); self.git('commit','-qm','seed')
        self.packet(b=B+b'\n-- contributor 1\n')
        c,d,e=self.call(); self.assertEqual((c,d['reused']),(0,[]),e)
        second = Fixture('test_nonlean_is_na')
        second.setUp()
        self.addCleanup(second.doCleanups)
        second.cache = self.cache
        second.write('README.md',b'separate workspace history\n')
        second.git('add','README.md'); second.git('commit','-qm','different head')
        second.packet(); second.git('commit','-qm','seed')
        self.assertNotEqual(self.git('rev-parse','HEAD'),second.git('rev-parse','HEAD'))
        second.packet(b=B+b'\n-- contributor 2\n')
        c,d,e=second.call(); self.assertEqual((c,d['elaborated'],d['reused']),(0,['StageB'],['StageA']),e)

    def test_pin_bound_small_external_bundle(self):
        self.actual()
        t=Path(self.tmp.name)
        ext=t/'external'; ext.mkdir()
        (ext/'External.lean').write_text('def stagedExternal : Nat := 17\n')
        subprocess.run([LEAN,*lint.FLAGS,'-R',str(ext),'-o',str(ext/'External.olean'),
                        str(ext/'External.lean')],check=True,cwd=ext,capture_output=True)
        (ext/'External.lean').unlink()
        self.packet(a=b'import External\n def stagedNat := stagedExternal - 12\n',
                    dependencies={'StageA':['External'],'StageB':['StageA']})
        _,fingerprint,_=lint.verified_compiler(LEAN,lint.sanitized_env())
        spec = lint.json_bytes({'version':1,'environment':fingerprint,'roots':['External'],
                'libraries':['external'],'files':{p.relative_to(t).as_posix():lint.digest(p.read_bytes())
                                               for p in ext.iterdir()}})
        (t/'upstream.json').write_bytes(spec)
        options=('--upstream',str(t),'--upstream-sha',lint.digest(spec))
        c,d,e=self.call(*options); self.assertEqual((c,d['elaborated']),(0,['StageA','StageB']),e)
        (ext/'External.olean').write_bytes(b'changed')
        c,d,e=self.call(*options); self.assertEqual(c,2,e); self.assertIn('changed upstream cache entry',e)

    def test_actual_non_kernel_error_is_failure(self):
        self.actual()
        self.packet(b=BROKEN)
        code,data,e=self.call(); self.assertEqual((code,data['status']),(1,'FAIL'),e)


if __name__=='__main__':
    unittest.main()
