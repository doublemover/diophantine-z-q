#!/usr/bin/env python3
"""Verify the exact checked source closure without relying on compiler artifacts."""
import argparse,hashlib,json,pathlib,re,sys
# This entrypoint is repository-scoped, regardless of the caller's cwd.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[4] / 'scripts'))
from check_lean import code_only

def has_constant_declaration(code):
 # Distinguish a command from a continuation such as `constant c (c i : ℚ) * t`.
 for match in re.finditer(r'^\s*(?:(?:private|public|protected|noncomputable)\s+)*constant\s+[A-Za-z_][\w.]*', code, re.M):
  tail = code[match.end():].lstrip()
  if tail.startswith('.{'): tail = tail[1:]
  while tail and tail[0] in '([{':
   stack=[]; end=None
   for i,c in enumerate(tail):
    if c in '([{': stack.append(c)
    elif c in ')]}':
     if not stack or '([{'.index(stack.pop()) != ')]}'.index(c): break
     if not stack: end=i+1; break
   if end is None: break
   tail=tail[end:].lstrip()
  if tail.startswith(':'): return True
 return False

def validate_source(text, label):
 code = code_only(text)
 assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by)\b', code), f'Forbidden proof escape: {label}'
 assert 'skipKernelTC' not in code, f'Kernel-check override: {label}'
 assert not has_constant_declaration(code), f'Unproved constant declaration: {label}'
 return code
def is_official_import(name):
 return name.split('.')[0] in {'Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ImportGraph','ProofWidgets'}

def validate_audit(text, order):
 validate_source(text, 'CheckpointAudit')
 # Import private declarations too; a regular import is insufficient for this audit.
 expected = 'module\n' + ''.join(f'import all {n}\n' for n in order)
 expected += 'import Lean.Util.CollectAxioms\n'
 assert text.startswith(expected), 'Audit must start with module then all private-inclusive imports in manifest order'
 arrays = re.findall(r'let modules : Array Name := #\[(.*?)\]', text, re.S)
 assert len(arrays) == 1, 'Audit must have one module selection array'
 assert re.findall(r'`([A-Za-z_][A-Za-z_0-9.]*)', arrays[0]) == order, 'Audit selection differs from manifest'
 assert text.count('\nmodule\n') == 0, 'Misplaced module header'

def main():
 if not __debug__: raise RuntimeError('Run without Python -O: validation assertions must be enabled')
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent,
   help='Progress source directory to validate, including a copied package; the verifier and parser stay repository-scoped')
 root=parser.parse_args().root.resolve()
 manifest=json.loads((root/'checkpoint-manifest.json').read_text())
 order=manifest['module_order'];seen=set()
 assert json.loads((root/'module-order.json').read_text())==order, 'Replay order differs from manifest'
 assert len(order)==len(set(order)) and set(order)==set(manifest['modules']), 'Manifest coverage mismatch'
 for m in order:
  p=root/(m+'.lean');raw=p.read_bytes()
  assert hashlib.sha256(raw).hexdigest()==manifest['modules'][m]['sha256'],f'Hash mismatch: {m}'
  text=validate_source(raw.decode(), m)
  for line in re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)',text,re.M):
   for dep in line.split('--')[0].split():
    if is_official_import(dep):continue
    assert dep in seen,f'Import not preceding consumer: {dep} -> {m}'
  seen.add(m)
 assert len(seen)==manifest['module_count']
 validate_audit((root/'CheckpointAudit.lean').read_text(), order)
 print(f'MANIFEST_PASS modules={len(seen)}; exact hashes, closed imports, topological order, strict source admission, no kernel overrides/placeholders/native evaluation')

if __name__ == '__main__': main()
