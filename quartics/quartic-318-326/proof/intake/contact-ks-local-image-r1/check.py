"""Replay only the exact SectionHeight donor and the new finite KS-image leaf."""
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import check_progress_lean as ci
from check_progress_experiment import audit_text

MANIFEST_SHA = '9c5320ce324cc5644a573e6760b2639b6cf2c95fd7af7d9488e3266c474b1036'
name_map = ('SectionHeight318', 'OriginalExactLocalKSUnit318')
if len(sys.argv) != 2 or sys.argv[1] not in {'targets', 'check'}:
    raise SystemExit('usage: check.py targets|check')
raw = (HERE / 'kernel.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA:
    raise ValueError('Unexpected exact donor/leaf manifest')
p = json.loads(raw)
if tuple(d['module'] for d in p['sources']) != name_map:
    raise ValueError('Unexpected source scope')
official, seen, src = set(), set(), []
for v in p['sources']:
    file = ROOT / v['path']
    if file.is_symlink() or file.suffix != '.lean' or file.stem != v['module']:
        raise ValueError(f'Invalid exact source path: {file}')
    b = file.read_bytes()
    if hashlib.sha256(b).hexdigest() != v['sha256']:
        raise ValueError(f'Changed pinned source: {file}')
    for d in ci.import_names(b.decode('utf-8')):
        if d.startswith('Mathlib.'):
            official.add(d)
        elif d not in seen:
            raise ValueError(f'Unreviewed or unordered local import: {d}')
    seen.add(v['module'])
    src.append(file)
if sorted(official) != p['stock']:
    raise ValueError('Unexpected stock targets')
if sys.argv[1] == 'targets':
    print(*sorted(official), sep='\n')
    raise SystemExit(0)
out = ROOT / 'build/contact-ks-local-image'
out.mkdir(parents=True, exist_ok=False)
lib = out / 'lib'
lib.mkdir()
env, version = ci.environment(ci.PROJECT, lib)
report = {'scope': p['profile'], 'source_pins': p, 'toolchain': version,
          'status': 'failed', 'checks': []}
try:
    for name, source in zip(name_map, src, strict=True):
        report['checks'].append(ci.compile_one(ci.PROJECT, env, name, source,
                                               lib / f'{name}.olean', out / 'logs',
                                               root=source.parent))
    audit = out / 'GaugeAudit.lean'
    audit.write_text(audit_text(list(name_map)), encoding='utf-8')
    ci.compile_one(ci.PROJECT, env, 'GaugeAudit', audit, None, out / 'logs', root=out)
    log = (out / 'logs/GaugeAudit.log').read_text(encoding='utf-8')
    m = re.search(r'EXPERIMENT_AUDIT_PASS declarations=([1-9][0-9]*) modules=2\b', log)
    if not m:
        raise RuntimeError('Missing complete recursive axiom audit')
    report.update(status='passed', audited_declarations=int(m[1]))
except Exception as e:
    report['error'] = str(e)
    for f in sorted((out / 'logs').glob('*.log')):
        lines = f.read_text(encoding='utf-8', errors='replace').splitlines()
        first = next((i for i,s in enumerate(lines) if 'error:' in s or 'error(' in s), None)
        if first is not None:
            print(f'{f.name}: first Lean failure', flush=True)
            print('\n'.join(lines[first:first+30]), flush=True)
    raise
finally:
    (out / 'RESULT.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
