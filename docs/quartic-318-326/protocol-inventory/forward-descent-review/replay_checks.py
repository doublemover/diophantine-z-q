#!/usr/bin/env python3
"""Replay byte bindings, not mathematical reasoning. No repository writes."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--workspace', type=Path, default=Path(__file__).resolve().parents[2])
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = args.workspace.resolve()
repo = root / 'diophantine-z-q'
target = root / 'recovery-contact-0358/forward-source-review'
checks = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def check(label, actual, expected):
    checks.append({'check': label, 'actual': actual, 'expected': expected, 'pass': actual == expected})

def excerpt(data, pin):
    return b''.join(data.splitlines(keepends=True)[pin['start_line']-1:pin['end_line']])

receipt_bytes = (target / 'receipt.json').read_bytes()
check('target receipt', sha(receipt_bytes), '29ce41891589b97b3ab36b129386410d264acc1807908cc322d387cd08aa2a53')
receipt = json.loads(receipt_bytes)
app_bytes = (target / 'APPLICATION.json').read_bytes()
check('target application', sha(app_bytes), '5440aca3aaf4a39e82cb09635b6855e12bf53e61777a977b7603274a8ab52715')
app = json.loads(app_bytes)
for path, expected in receipt['artifacts_sha256'].items():
    check('target artifact: ' + path, sha((target / path).read_bytes()), expected)

historical_path = 'docs/quartic-318-326/v13-consumer-binding/arithmetic.before.md'
historical = (repo / historical_path).read_bytes()
check('preserved historical arithmetic snapshot', sha(historical), '9737d56476c98677624725fc61bb36433ed008b2636a22d423cef8c1c02ee518')
for pin in app['bound_passages']:
    data = historical if pin['path'].endswith('/docs/arithmetic.md') else (repo / pin['path']).read_bytes()
    check('bound whole: ' + pin['role'], sha(data), pin['whole_sha256'])
    check('bound excerpt: ' + pin['role'], sha(excerpt(data, pin)), pin['excerpt_sha256'])

comparison = json.loads((target / 'version-comparison.json').read_bytes())
for pair in comparison['raw_byte_comparisons']:
    extracts = []
    for version in ['v11', 'v13']:
        pin = pair[version]
        data = (repo / pin['path']).read_bytes()
        check(version + ' whole: ' + pair['role'], sha(data), pin['whole_sha256'])
        part = excerpt(data, pin)
        extracts.append(part)
        check(version + ' excerpt: ' + pair['role'], sha(part), pin['excerpt_sha256'])
    check('cross-version bytes: ' + pair['role'], extracts[0] == extracts[1], True)

for pin in app['related_immutable_receipts']:
    check('related receipt: ' + pin['path'], sha((target / pin['path']).read_bytes()), pin['sha256'])
finite_root = target.parent / 'v11-completeness-consumer'
finite = json.loads((finite_root / 'finite-joins-receipt.json').read_bytes())
for path, expected in finite['sha256'].items():
    check('finite-join text: ' + path, sha((finite_root / path).read_bytes()), expected)
for path, expected in finite['source_sha256'].items():
    check('finite component: ' + path, sha((repo / path).read_bytes()), expected)

current_path = 'quartics/quartic-318-326/docs/arithmetic.md'
current = (repo / current_path).read_bytes()
check('current arithmetic snapshot', sha(current), '069738d42a127a2cd3a476cba9281a77f3cbd23ec81a5a3441090ea8ebab09d0')
current_lines = current.splitlines(keepends=True)
old_lines = historical.splitlines(keepends=True)
check('pre-Kato text unchanged', current_lines[:1593], old_lines[:1593])
# Do not put the full text into JSON; replace equal-byte results by their hashes.
checks[-1]['actual'] = sha(checks[-1]['actual'] if isinstance(checks[-1]['actual'], bytes) else b''.join(checks[-1]['actual']))
checks[-1]['expected'] = sha(b''.join(old_lines[:1593]))
check('post-adoption retained text unchanged', sha(b''.join(current_lines[1601:])), sha(b''.join(old_lines[1599:])))
for pin in app['bound_passages']:
    if pin['role'] == 'final_scalar_local_inputs':
        check('current scalar excerpt unchanged', sha(excerpt(current, pin)), pin['excerpt_sha256'])
needle = b'The exact restricted-converse, simultaneous-descent and pole/witness consumers'
old_final = next(line for line in old_lines if line.startswith(needle))
new_final = next(line for line in current_lines if line.startswith(needle))
check('exact final 288-row paragraph unchanged', sha(new_final), sha(old_final))

# Compare the actual PDF content streams, not an OCR rendering.
import fitz
with fitz.open(target / 'primary/icm1990-volume1.pdf') as full, fitz.open(target / 'primary/kolyvagin-published-429-436.pdf') as part:
    check('Kolyvagin extracted page count', len(part), 8)
    for i in range(8):
        a = b''.join(full.xref_stream(x) for x in full[516+i].get_contents())
        b = b''.join(part.xref_stream(x) for x in part[i].get_contents())
        check('ICM source page content: ' + str(517+i), sha(a), sha(b))

old_head_blob = subprocess.check_output(['git', 'show', app['observed_repository_head'] + ':' + current_path], cwd=repo)
delta = ''.join(difflib.unified_diff(historical.decode().splitlines(keepends=True), current.decode().splitlines(keepends=True), fromfile=historical_path, tofile=current_path))
result = {
    'kind': 'independent byte-binding replay, not mathematical proof',
    'all_pass': all(c['pass'] for c in checks),
    'check_count': len(checks),
    'observed_current_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
    'historical_snapshot': {'path': historical_path, 'sha256': sha(historical)},
    'target_observed_head': app['observed_repository_head'],
    'target_head_arithmetic_blob_sha256': sha(old_head_blob),
    'provenance_clarification': 'The target arithmetic hash binds the reviewed uncommitted historical snapshot, not the arithmetic blob at its observed HEAD. The exact snapshot is preserved and independently checked.',
    'current_arithmetic': {'path': current_path, 'sha256': sha(current)},
    'current_delta': delta,
    'checks': checks,
}
serialized = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
if args.output:
    args.output.write_text(serialized, encoding='utf-8')
else:
    print(serialized, end='')
raise SystemExit(0 if result['all_pass'] else 1)
