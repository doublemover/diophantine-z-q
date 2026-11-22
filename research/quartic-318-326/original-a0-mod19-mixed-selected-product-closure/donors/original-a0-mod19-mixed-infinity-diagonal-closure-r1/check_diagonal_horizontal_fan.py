"""Exact finite ray, monomial and balance check; no key computation."""
import json
rays=[(n,n-1) for n in range(1,17)]+[(1,1),(0,1)]
wall=(16,15)
def det(u,v): return u[0]*v[1]-u[1]*v[0]
assert len(rays)==18 and all(det(a,b)==1 for a,b in zip(rays,rays[1:]))
assert rays[1]==(2,1)
assert all((u+1,v+1)==n for (u,v),n in zip(rays[:15],rays[1:16]))
def weight(v): return 16*v[1]-15*v[0]
assert [r for r in rays if weight(r)==0]==[wall]
for a,b in rays:
    if weight((a,b))<=0:
        # Strip by (r/Q)^32; each lower power and the secondary pole.
        assert a-b>0 and 15*a-16*b>=0
        assert all((32-2*j)*(a-b)>0 for j in range(16))
    if weight((a,b))>=0:
        # Strip by r^2; each lower power has positive order if a>0.
        assert 16*b-15*a>=0
        assert all(2*a+2*j*(b-a)>=0 for j in range(16))
        if a:
            assert all(2*a+2*j*(b-a)>0 for j in range(16))
assert det((1,-1),(-15,16))==1
assert (16*1-15, -15*16+16*15)==(1,0)
print(json.dumps(dict(rays=rays,adjacent_determinants=[det(a,b) for a,b in zip(rays,rays[1:])],
    sign=[weight(v) for v in rays],wall=wall,balanced_orbit_characters=[[1,-1],[-15,16]],
    off_wall_strip='unit; delta=1 on the geometric special fibre',
    root_toroid='A B = pi^(2e) R^64'),indent=2))
