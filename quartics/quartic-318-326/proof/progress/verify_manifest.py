#!/usr/bin/env python3
"""Verify the exact checked source closure without relying on compiler artifacts."""
import hashlib,json,pathlib,re,sys
def validate_audit(text, order):
 # Import private declarations too; a regular import is insufficient for this audit.
 expected = 'module\n' + ''.join(f'import all {n}\n' for n in order)
 expected += 'import Lean.Util.CollectAxioms\n'
 assert text.startswith(expected), 'Audit must start with module then all private-inclusive imports in manifest order'
 arrays = re.findall(r'let modules : Array Name := #\[(.*?)\]', text, re.S)
 assert len(arrays) == 1, 'Audit must have one module selection array'
 assert re.findall(r'`([A-Za-z_][A-Za-z_0-9.]*)', arrays[0]) == order, 'Audit selection differs from manifest'
 assert text.count('\nmodule\n') == 0, 'Misplaced module header'

def main():
 root=pathlib.Path(__file__).resolve().parent
 manifest=json.loads((root/'checkpoint-manifest.json').read_text())
 order=manifest['module_order'];seen=set()
 assert json.loads((root/'module-order.json').read_text())==order, 'Replay order differs from manifest'
 assert len(order)==len(set(order)) and set(order)==set(manifest['modules']), 'Manifest coverage mismatch'
 for m in order:
  p=root/(m+'.lean');raw=p.read_bytes()
  assert hashlib.sha256(raw).hexdigest()==manifest['modules'][m]['sha256'],f'Hash mismatch: {m}'
  text=raw.decode()
  assert not re.search(r'\b(sorry|admit|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)),f'Forbidden placeholder/evaluator: {m}'
  for line in re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?([^\n]+)',text,re.M):
   for dep in line.split('--')[0].split():
    if dep.startswith(('Mathlib','Lean','Batteries','Qq','Aesop','Plausible')):continue
    assert dep in seen,f'Import not preceding consumer: {dep} -> {m}'
  seen.add(m)
 assert len(seen)==manifest['module_count']
 validate_audit((root/'CheckpointAudit.lean').read_text(), order)
 print(f'MANIFEST_PASS modules={len(seen)}; exact hashes, closed imports, topological order, no placeholders/native evaluation')

if __name__ == '__main__': main()
