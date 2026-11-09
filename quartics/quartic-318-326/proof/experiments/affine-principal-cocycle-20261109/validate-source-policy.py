#!/usr/bin/env python3
"""Validate this eleven-source affine structure cohomology continuation against baseline.

This is the repository source/import policy, not an independent proof review.
The temporary composite does not alter any shared manifest or source packet.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'scripts/check_progress_experiment.py').is_file())
sys.path.insert(0, str(ROOT / 'scripts'))
import check_progress_lean as ci
import check_progress_experiment as experiment

BASE = '5e483a2b186a83500f4b603f3ddfc514ae84a393'
PREFIX = 'quartics/quartic-318-326/proof/progress/'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    current = json.loads((HERE / 'intake.json').read_text())
    with tempfile.TemporaryDirectory(prefix='affine-cohomology-policy-') as tmp:
        root = Path(tmp)
        baseline = root / 'baseline'
        baseline.mkdir()
        for filename in ['checkpoint-manifest.json', 'module-order.json',
                         'CheckpointAudit.lean', 'lean-toolchain', 'lake-manifest.json']:
            content = subprocess.check_output(['git', 'show', BASE + ':' + PREFIX + filename], cwd=ROOT)
            (baseline / filename).write_bytes(content)
        manifest = json.loads((baseline / 'checkpoint-manifest.json').read_text())
        for module in manifest['module_order']:
            name = module.replace('.', '/') + '.lean'
            target = baseline / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ci.PROJECT / name)
        plan = ci.derive_plan(baseline, early_depth=7)
        composite = root / 'composite'
        composite.mkdir()
        files = current['files']
        order = current['order']
        for folder, data in [(HERE, current)]:
            for filename in data['files']:
                shutil.copyfile(folder / filename, composite / filename)
        (composite / 'intake.json').write_text(json.dumps({'order': order, 'files': files}))
        _, _, direct, external = experiment.packet('composite', plan, root=root)
        needed = experiment.required_baseline(plan, direct)
        result = {
            'status': 'SOURCE_POLICY_PASS',
            'policy': 'scripts/check_progress_experiment.py packet(), on the eleven-source packet (nine new, two exact copies)',
            'baseline_commit': BASE,
            'baseline_snapshot': plan['snapshot'],
            'baseline_modules': len(plan['module_order']),
            'new_sources': {n: row['sha256'] for n, row in current['files'].items()},
            'direct_predecessors': {n: sha(ci.PROJECT / (n + '.lean')) for n in sorted(direct)},
            'required_predecessor_count': len(needed),
            'required_predecessor_sources': {n: sha(ci.PROJECT / (n + '.lean')) for n in needed},
            'external_imports': sorted(external),
            'source_acceptance': False,
            'shared_manifest_changed': False,
        }
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
