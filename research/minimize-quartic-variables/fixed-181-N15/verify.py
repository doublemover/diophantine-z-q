"""Offline replay of the fixed N=15 polynomial and its independently certified transfer."""
from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'SHA256SUMS.json').read_bytes())
assert all(sha(p/n)==h for n,h in manifest.items())
review=json.loads((p/'INDEPENDENT-FIXED-181-REVIEW.json').read_bytes())
for n,h in review['hashes'].items():
 if n=='check.py':
  assert h=='addc3299a2bbbe48ae532beb7232bb17e60bd7630bbbf11b0270f5f9c6cebf19'
  assert sha(p/n)=='f5f4ea197d3fa63dd8e8fc12975f6316680f66ba22cbdf98da4f8322d1721dd6'
 else: assert sha(p/n)==h
for args in [['donor182/verify.py'],['cold181.py','.', 'donor182'],['check.py']]:
 subprocess.run([sys.executable,'-IB',*args],cwd=p,check=True)
print('PASS: fixed N=15, 181 total variables, three independent offline replay steps complete.')
