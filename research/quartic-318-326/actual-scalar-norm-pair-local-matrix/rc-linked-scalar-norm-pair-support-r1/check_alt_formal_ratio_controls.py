"""Finite split/inert precision checks of all branches of U(mP)/U(P)."""
import contextlib,io,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'rc-linked-scalar-higher-descent-r1'))
saved_args=sys.argv[:]
sys.argv[:]=[sys.argv[0],'100']
with contextlib.redirect_stdout(io.StringIO()):
    import check_materialized_xi_new_primes as F
sys.argv[:]=saved_args
C=F.C
out=[]
for p,t,o,index,multiple,case in [
    (23,5,6,C.h,C.shift//C.h,'actual O'),
    (1279,1050,640,C.h,C.shift//C.h,'actual Tpm'),
    (23,18,6,3,2,'nonactual T0 control'),
]:
    model=C.E(p,t)
    assert model.order()==o
    point=model.nsmul(index%o)
    if case.endswith('O'): assert point is None
    else:
        assert point is not None and point[1]==0
        assert bool(point[0])==case.endswith('Tpm')
    u,v=[F.F.refine_split(p,j,o,t) for j in (index,index*multiple)]
    assert u%p==v%p==0 and u
    ratio=v//p*pow(u//p,-1,p)%p
    sign=-1 if case.endswith('Tpm') else 1
    assert ratio==(sign*multiple)%p
    out.append(dict(prime=p,root=t,order=o,case=case,chart=[u,v],ratio=ratio))
p,o=19,20
e,=C.places(p)
assert e.order()==o and e.nsmul(C.h%o) is None
u,v=[F.refine_inert(p,j,o) for j in (C.h,C.shift)]
m=C.shift//C.h
assert all(a%p==0 for a in u+v) and any(u)
assert tuple(m*a%(p*p) for a in u)==v
out.append(dict(prime=p,root=None,order=o,case='actual inert O',chart=[u,v],ratio=m%p))
print(json.dumps(out,indent=2))
