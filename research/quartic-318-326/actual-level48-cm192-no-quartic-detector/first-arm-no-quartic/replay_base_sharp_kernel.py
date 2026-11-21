#!/usr/bin/env python3
"""Exact published deleted sharp cores: zero 17/q0 component norm test."""
import json

cores={
"+":[1921,128,292,512,48,20,1024,3,5,9,65],
"-":[897,254,346,638,78,106,126,3,5,9],
}
out={}
for k,rows in cores.items():
    d=len(rows)
    def kernel(x):
        return all((x&r).bit_count()%2==0 for r in rows)
    ker=[x for x in range(1<<d) if kernel(x)]
    assert ker==[0]
    assert all(row < 1<<d for row in rows)
    out[k]={"dimension":d,"bit_zero_place":17,"deleted_place":"q0",
            "rows":rows,"kernel":ker,"kernel_with_zero_17_bit":[x for x in ker if x%2==0]}
print(json.dumps(out,sort_keys=True,indent=2))
