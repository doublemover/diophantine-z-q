"""Cold/warm/failure controls for tooling caches, separate from proof admission."""
import os
import json
import normalize_progress_bundles as bundles
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / '.github/actions'
SCRIPT = ROOT / 'scripts/setup_pinned_lean.sh'
PIN = 'leanprover/lean4:v4.35.0'
VERSION = 'Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)'


class ToolingTests(unittest.TestCase):
    def test_python_restored_before_setup_and_saved_before_project_work(self):
        s = (ACTION / 'setup-pinned-python/action.yml').read_text()
        self.assertLess(s.index('actions/cache/restore@'), s.index('actions/setup-python@'))
        self.assertLess(s.index('Verify exact'), s.index('actions/cache/save@'))
        self.assertIn('runner.tool_cache }}/Python/${{ inputs.python-version }}', s)
        self.assertIn('check-latest: false', s)
        self.assertNotIn('restore-keys:', s)
        for part in ['runner.os', 'runner.arch', 'steps.platform.outputs.image', 'inputs.python-version']:
            self.assertIn(part, s)

    def test_lean_cache_is_exact_tooling_only_and_saved_early(self):
        s = (ACTION / 'setup-pinned-lean/action.yml').read_text()
        self.assertEqual(s.count('actions/cache/restore@'), 2)
        self.assertEqual(s.count('actions/cache/save@'), 2)
        self.assertNotIn('restore-keys:', s)
        self.assertNotIn('path: ~/.elan\n', s)
        self.assertNotIn('path: .lake', s)
        self.assertNotIn('progress-ci', s)
        self.assertLess(s.index('Save checked installer'), s.index('- id: toolchain'))
        self.assertIn('leanprover--lean4---v4.35.0', s)
        self.assertIn('eb6cafb7290e8bd5f2937522d8d804f58f02bafc', s)

    def test_workflows_share_setup_and_warm_before_fanout(self):
        for p in (ROOT / '.github/workflows').glob('*.yml'):
            s = p.read_text()
            self.assertNotIn('uses: actions/setup-python@', s, p.name)
            self.assertNotIn('uses: actions/setup-node@', s, p.name)
            self.assertNotIn('curl --fail --location --retry 3 -o elan.tar.gz', s, p.name)
        for name, later in [('progress-lean.yml', '  foundation:'), ('progress-experiments.yml', '  first-check:')]:
            s = (ROOT / '.github/workflows' / name).read_text()
            self.assertLess(s.index('Warm pinned compiler cache'), s.index(later))
            self.assertIn("'.github/actions/setup-pinned-*/**'", s)
        experiment = (ROOT / '.github/workflows/progress-experiments.yml').read_text()
        self.assertNotIn('uses: actions/cache/save@', experiment)
        self.assertIn("if: steps.plan.outputs.has_packets == 'true'", experiment)

    def test_external_actions_remain_commit_pinned(self):
        for p in list((ROOT / '.github/workflows').glob('*.yml')) + list(ACTION.glob('*/action.yml')):
            for action in re.findall(r'uses: ([^\s]+)', p.read_text()):
                if not action.startswith('./'):
                    self.assertRegex(action, r'^[\w/-]+@[0-9a-f]{40}$', p.name)

    def test_runtime_restore_transport_failure_does_not_skip_validation(self):
        for name in ['python', 'node', 'lean', 'tectonic']:
            text = (ACTION / f'setup-pinned-{name}/action.yml').read_text()
            for block in re.split(r'(?m)^    - ', text):
                if 'actions/cache/restore@' in block:
                    self.assertIn('continue-on-error: true', block)
                elif 'continue-on-error:' in block:
                    self.fail('Only optional cache restore transport may be ignored')
            self.assertNotIn('outputs.cache-primary-key', text)

    def test_node_and_tectonic_pins_and_scopes(self):
        node = (ACTION / 'setup-pinned-node/action.yml').read_text()
        self.assertIn('runner.tool_cache }}/node/${{ inputs.node-version }}', node)
        self.assertIn('package-manager-cache: false', node)
        self.assertIn('process.versions.node !== process.env.EXPECTED_NODE', node)
        tectonic = (ACTION / 'setup-pinned-tectonic/action.yml').read_text()
        self.assertIn('path: .tools/tectonic-0.17.0/*.tar.gz', tectonic)
        self.assertIn('exe=p.install()', tectonic)
        self.assertNotIn('path: .cache/tectonic', tectonic)

    def test_single_artifact_layout_is_normalized_without_byte_changes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            raw = b'{"status":"PASS","cohort":0}'
            (root/'receipt.json').write_bytes(raw)
            (root/'lib').mkdir(); (root/'lib/A.olean').write_bytes(b'original bytes')
            self.assertTrue(bundles.normalize(root))
            self.assertEqual((root/'progress-cohort-0/receipt.json').read_bytes(),raw)
            self.assertEqual((root/'progress-cohort-0/lib/A.olean').read_bytes(),b'original bytes')
            self.assertFalse(bundles.normalize(root))

    def test_failed_and_mixed_artifact_layouts_fail_closed(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for row in [{'status':'FAILED','cohort':0}, {'status':'PASS','cohort':'../bad'},
                        {'status':'PASS','cohort':True}]:
                (root/'receipt.json').write_text(json.dumps(row))
                with self.assertRaises(ValueError): bundles.normalize(root)
            (root/'receipt.json').write_text('{"status":"PASS","cohort":0}')
            (root/'progress-cohort-1').mkdir()
            with self.assertRaises(ValueError): bundles.normalize(root)

    def test_multiple_artifacts_and_download_workflow_joins(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for i in [0,1]:
                (root/f'progress-cohort-{i}').mkdir()
            self.assertFalse(bundles.normalize(root))
        text = (ROOT/'.github/workflows/progress-lean.yml').read_text()
        self.assertEqual(text.count('run: python -B scripts/normalize_progress_bundles.py '),3)
        self.assertEqual(text.count('name: progress-failure-attempt-'),3)
        self.assertEqual(text.count('name: Upload verified cohort\n        if: success()'),3)

    def fixture(self, root):
        home = root / 'home'; home.mkdir()
        bin = home / '.elan/bin'; bin.mkdir(parents=True)
        tool = home / '.elan/toolchains/leanprover--lean4---v4.35.0/bin'
        for rel in ['lean/lean-toolchain', 'quartics/quartic-318-326/proof/progress/lean-toolchain']:
            p = root / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(PIN+'\n')
        env = dict(os.environ, HOME=str(home), RUNNER_TEMP=str(root/'temp'), GITHUB_PATH=str(root/'path'))
        return home, bin, tool, env

    def executable(self, path, body):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('#!/bin/bash\nset -eu\n'+body+'\n'); path.chmod(0o755)

    def test_warm_toolchain_never_installs_or_downloads(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); _, bin, tool, env = self.fixture(root)
            self.executable(tool/'lean', 'exit 0')
            self.executable(bin/'elan', 'echo UNEXPECTED_INSTALL; exit 91')
            self.executable(bin/'lean', f'echo "{VERSION}"')
            self.executable(bin/'lake', 'echo "Lake version 5.0.0"')
            result = subprocess.run(['bash',str(SCRIPT),'toolchain'],cwd=root,env=env,text=True,capture_output=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('UNEXPECTED_INSTALL',result.stdout)

    def test_cold_toolchain_installs_exact_pin_then_verifies(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); _, bin, tool, env = self.fixture(root)
            self.executable(bin/'elan', f'test "$1" = toolchain; test "$2" = install; test "$3" = {PIN}; echo COLD_INSTALL')
            self.executable(bin/'lean', f'echo "{VERSION}"')
            self.executable(bin/'lake', 'echo "Lake version 5.0.0"')
            result = subprocess.run(['bash',str(SCRIPT),'toolchain'],cwd=root,env=env,text=True,capture_output=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertIn('COLD_INSTALL',result.stdout)

    def test_wrong_compiler_and_changed_pin_fail_closed(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); _, bin, tool, env = self.fixture(root)
            self.executable(tool/'lean', 'exit 0')
            self.executable(bin/'lean', 'echo "Lean version 4.34.0, badcommit"')
            self.executable(bin/'lake', 'echo UNEXPECTED_LAKE')
            result = subprocess.run(['bash',str(SCRIPT),'toolchain'],cwd=root,env=env,text=True,capture_output=True)
            self.assertNotEqual(result.returncode,0)
            self.assertNotIn('UNEXPECTED_LAKE',result.stdout)
            (root/'lean/lean-toolchain').write_text('unapproved-pin\n')
            result = subprocess.run(['bash',str(SCRIPT),'toolchain'],cwd=root,env=env,text=True,capture_output=True)
            self.assertNotEqual(result.returncode,0)

    def test_corrupt_cached_installer_is_not_executed_or_redownloaded(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); home, _, _, env = self.fixture(root)
            archive = home/'.cache/pinned-elan/4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz'
            archive.parent.mkdir(parents=True); archive.write_bytes(b'corrupt cached archive')
            result = subprocess.run(['bash',str(SCRIPT),'installer'],cwd=root,env=env,text=True,capture_output=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('FAILED',result.stdout)
            self.assertFalse((root/'temp/elan-install/elan-init').exists())

    def test_shell_syntax(self):
        subprocess.run(['bash','-n',str(SCRIPT)],check=True)


if __name__ == '__main__': unittest.main()
