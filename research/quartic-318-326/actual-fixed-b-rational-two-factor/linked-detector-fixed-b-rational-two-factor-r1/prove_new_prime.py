#!/usr/bin/env python3
"""Call the pinned deterministic FLINT proved-prime API (not BPSW)."""
from pathlib import Path
from hashlib import sha256
import json
import flint
P=Path(__file__).resolve().parent/'EXACT-RATIONAL-TWO-FACTOR-W.json'
z=json.loads(P.read_bytes())
q=z['qa']
assert flint.__version__=='0.8.0'
assert flint.__FLINT_VERSION__=='3.3.1'
assert q.bit_length()==3505 and len(str(q))==1055
assert flint.fmpz(q).is_prime()==1
print(json.dumps(dict(p_sha256=sha256(str(q).encode()).hexdigest(),
      bit_length=q.bit_length(),python_flint=flint.__version__,
      FLINT=flint.__FLINT_VERSION__,proved_prime=True),indent=2))
