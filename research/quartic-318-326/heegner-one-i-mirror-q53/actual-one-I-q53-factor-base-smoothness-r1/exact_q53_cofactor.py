#!/usr/bin/env python3
"""Emit just the pinned C decimal to the exact segmented sieve."""
from pathlib import Path
import hashlib, json
p=Path(__file__).resolve().parent.parent/'actual-one-I-q53-global-norm-r1'/'ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json'
v=p.read_bytes()
assert hashlib.sha256(v).hexdigest()=='31adfcc272aaf806a8cb3838ff58b7d33f5ab3fc1e94dbfd9ad043b79d445079'
print(json.loads(v)['unfactored_cofactor'])
