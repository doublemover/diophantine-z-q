from itertools import product
import json

p=11
lines=[(1,t) for t in range(p)]+[(0,1)]
counts=[0]*len(lines)
bad_by_number=[0]*(len(lines)+1)
inverses=0
for a,b,c,d in product(range(p),repeat=4):
    bad=[i for i,(x,y) in enumerate(lines) if (x*a+y*c)%p==0 and (x*b+y*d)%p==0]
    for i in bad:
        counts[i]+=1
    z=(a*d-b*c)%p
    assert bool(bad)==(z==0)
    assert len(bad) in (0,1,12)
    assert (len(bad)==12)==(a==b==c==d==0)
    bad_by_number[len(bad)]+=1
    if not bad:
        k=pow(z,-1,p)
        A,B,C,D=(k*d,-k*b,-k*c,k*a)
        assert ((a*A+b*C)%p,(a*B+b*D)%p,(c*A+d*C)%p,(c*B+d*D)%p)==(1,0,0,1)
        inverses+=1
assert counts==[p*p]*12 and bad_by_number[0]==(p*p-1)*(p*p-p)
assert bad_by_number[1]==12*(p*p-1) and bad_by_number[12]==1
crt=[]
for u in range(33):
    v=[22*u%33,12*u%33]
    assert sum(v)%33==u and v[0]%3==u%3 and v[1]%11==u%11
    assert v[0]%11==0 and v[1]%3==0
    crt.append(v)
print(json.dumps({"bad_one_direction":bad_by_number[1],"good":bad_by_number[0],
    "kernel_cardinalities":counts,"line_rows":lines,"operator_inverse_controls":inverses,
    "projectors_mod_33":crt,"zero_shared":bad_by_number[12]},indent=2,sort_keys=True))
