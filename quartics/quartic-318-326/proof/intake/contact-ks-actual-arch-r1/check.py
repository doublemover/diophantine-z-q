"""Focused compilation using only authenticated, pre-existing project artifacts."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import check_progress_lean as ci
from check_progress_experiment import required_baseline, restore_baseline, audit_text

MANIFEST_SHA = '7c43d692c242333c89b5f86d16015aa61dbb15277d3ecfa297a631122afd152f'
if len(sys.argv) != 2 or sys.argv[1] not in {'targets', 'check'}:
    raise SystemExit('usage: check.py targets|check')
raw = (HERE / 'kernel.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA:
    raise ValueError('Unexpected exact restore manifest')
p = json.loads(raw)
if subprocess.check_output(['git', 'rev-parse', 'HEAD:quartics/quartic-318-326/proof/progress'],
                           cwd=ROOT, text=True).strip() != p['progress_tree']:
    raise ValueError('Accepted Progress source tree diverged from the exact historical donor')
plan = ci.derive_plan(early_depth=7)
if (plan['base'], plan['snapshot']) != (p['base'], p['snapshot']):
    raise ValueError('Accepted snapshot or checker metadata diverged')
sources = []
direct_model = set()
downstream, seen = set(), set()
for d in p['sources']:
    f = ROOT / d['path']
    if f.is_symlink() or f.stem != d['module'] or ci.sha(f) != d['sha256']:
        raise ValueError(f'Wrong exact leaf bytes: {f}')
    for dep in ci.import_names(f.read_text(encoding='utf-8')):
        if dep.startswith('Mathlib.'):
            downstream.add(dep)
        elif dep in plan['module_keys']:
            direct_model.add(dep)
        elif dep not in seen:
            raise ValueError(f'Undeclared source dependency: {dep}')
    seen.add(d['module'])
    sources.append((d['module'], f))
if direct_model != {'SectionHeight318', 'RefinedContactRealization318', 'GlobalSectionNorm318'}:
    raise ValueError('Unexpected accepted dependency scope')
needed = required_baseline(plan, direct_model)
if sorted(needed) != p['modules']:
    raise ValueError('Unexpected accepted transitive artifacts')
for n in needed:
    f = ci.PROJECT / (n.replace('.', '/') + '.lean')
    downstream.update(d for d in ci.import_names(f.read_text(encoding='utf-8'))
                      if d.startswith('Mathlib.'))
if sorted(downstream) != p['stock']:
    raise ValueError('Unexpected stock roots')
if sys.argv[1] == 'targets':
    print(*sorted(downstream), sep='\n')
    raise SystemExit(0)
out = ROOT / 'build/contact-ks-actual-arch'
out.mkdir(parents=True, exist_ok=False)
lib = out / 'lib'
lib.mkdir()
report = {'scope': p['scope'], 'restored_snapshot': p['snapshot'],
          'verified_predecessor_count': 0, 'status': 'failed', 'checks': []}
try:
    cache = ROOT / '.cache/progress-ci'
    if not (cache / 'receipt.json').is_file():
        raise ValueError('Exact matching audited cache is unavailable; no rebuild attempted')
    report['verified_predecessor_count'] = len(restore_baseline(cache, lib, plan, needed))
    env, version = ci.environment(ci.PROJECT, lib)
    report['toolchain'] = version
    for n, s in sources:
        report['checks'].append(ci.compile_one(ci.PROJECT, env, n, s, lib/(n+'.olean'),
                                               out/'logs', root=s.parent))
    audit = out/'GaugeAudit.lean'
    audit.write_text(audit_text([n for n, _ in sources]), encoding='utf-8')
    ci.compile_one(ci.PROJECT, env, 'GaugeAudit', audit, None, out/'logs', root=out)
    log = (out/'logs/GaugeAudit.log').read_text(encoding='utf-8')
    match = re.search(r'EXPERIMENT_AUDIT_PASS declarations=([1-9][0-9]*) modules=3\b', log)
    if not match:
        raise ValueError('Missing exact leaf axiom audit')
    report.update(status='passed', audited_declarations=int(match[1]))
except Exception as err:
    report['error'] = str(err)
    for f in sorted((out/'logs').glob('*.log')):
        lines = f.read_text(encoding='utf-8', errors='replace').splitlines()
        i = next((i for i,s in enumerate(lines) if 'error:' in s or 'error(' in s), None)
        if i is not None:
            print(f'{f.name}: first Lean failure', flush=True)
            print('\n'.join(lines[i:i+35]), flush=True)
    raise
finally:
    (out/'RESULT.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
