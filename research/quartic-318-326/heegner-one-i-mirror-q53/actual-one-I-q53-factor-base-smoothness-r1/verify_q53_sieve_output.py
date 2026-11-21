#!/usr/bin/env python3
"""Cross-check exact coverage count, no extracted factors and remaining support."""
from pathlib import Path
import json,hashlib
from math import prod
import sympy as s
H=Path(__file__).resolve().parent
src=(H.parent/'actual-one-I-q53-global-norm-r1'/'ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json').read_bytes()
assert hashlib.sha256(src).hexdigest()=='31adfcc272aaf806a8cb3838ff58b7d33f5ab3fc1e94dbfd9ad043b79d445079'
C=json.loads(src)['unfactored_cofactor']
out=json.loads((H/'EXACT-Q53-COMPLEMENT-150M-SIEVE.json').read_bytes())
R=int(out['remaining'])
assert out['maximum']==150000000
assert int(s.primepi(out['maximum']))==out['prime_tests']==8444396
assert C==R*prod(p**e for p,e in out['factors'])
assert not out['factors'] and R==C and (R%53,pow(R,4,53))==(21,24)
