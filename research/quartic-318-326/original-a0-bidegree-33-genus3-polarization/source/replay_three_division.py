import json
a2,a4=-4,16
poly=[3,4*a2,6*a4,0,-a4*a4]
assert poly==[3,-16,96,0,-256]
values=[sum(c*u**(4-i) for i,c in enumerate(poly))%5 for u in range(5)]
assert values==[4,2,3,4,4]
assert 3%5 and all(values)
out=dict(normalized_division_coefficients=poly,reduction_prime=5,residues=values,
         rational_root=False,scope="fixed normalized polynomial; no scalar support test")
print(json.dumps(out,indent=2,sort_keys=True))
