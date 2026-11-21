#!/usr/bin/env python3
"""Read the plain-disc counterparts of two eta coordinates on the exact 13 slice."""
import importlib.util
from collections import Counter
import hashlib
import json
from pathlib import Path
from sys import argv

if len(argv) != 2:
    raise SystemExit("pass the exact check_sparse_atkin_13.py donor path")
p=Path(argv[1])
assert hashlib.sha256(p.read_bytes()).hexdigest() == "1bedcf9672b3f128f5549e53cbb32430e4d45fb000f840aba4e32826b6d5ecaa"
s=importlib.util.spec_from_file_location("atkin_donor",p)
m=importlib.util.module_from_spec(s)
s.loader.exec_module(m)
_, fixed, _=m.initial()
tables=m.build()
rows={}
w_keys={}
for j in range(2400):
    ds, key, _=m.evaluate(fixed[:-1]+(j,),tables)
    _, U, _=m.invariants(ds)
    w_keys[j]=key
    # Masks denote negative signs; the eta root is deliberately not recovered.
    rows[j]=tuple(m.a(U[i],m.pw(U[i],13))[0] for i in (127,126))
assert len(set(w_keys.values()))==2400
alias=[(521,1601),(769,2129),(847,1768),(902,1594),(1125,1239),(1370,1407)]
assert all(rows[i]==rows[j] and w_keys[i]!=w_keys[j] for i,j in alias)
buckets=sorted(Counter(rows.values()).items())
assert len(buckets)==16
ledger=json.dumps([[j, rows[j],w_keys[j]] for j in rows],separators=(",",":"))
obj={"masks":[127,126],"distinct_literal_W_orbits":len(set(w_keys.values())),
     "value_pair_count":len(buckets),"buckets":buckets,
     "prior_all_U_aliases_persist":[[i,j,rows[i]] for i,j in alias],
     "selected_controls":[[j,rows[j],w_keys[j]] for j in (0,1,37,521,1601)],
     "all_rows_sha256":hashlib.sha256(ledger.encode()).hexdigest()}
print(json.dumps(obj,indent=2,sort_keys=True))
