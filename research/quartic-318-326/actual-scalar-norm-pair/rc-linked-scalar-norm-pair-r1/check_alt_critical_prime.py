"""Replay the single alternate-cut critical prime 83 at fixed actual h,J."""
import contextlib,io,json,sys
from pathlib import Path
s=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(s/'rc-linked-scalar-higher-descent-r1'))
args=sys.argv[:]
sys.argv=[sys.argv[0],'100']
with contextlib.redirect_stdout(io.StringIO()):
    import check_materialized_xi_new_primes as F
sys.argv=args
C=F.C
p=83
e,=C.places(p);o=e.order()
assert o==84 and all(p%d for d in range(2,10))
u=F.refine_inert(p,C.h,o)
v=F.refine_inert(p,C.shift,o)
m=p*p
H=(u[0]**2-2*u[1]**2)%m; I=(v[0]**2-2*v[1]**2)%m; f=(u[0]**2+2*u[1]**2)%m
Q=I*pow(H*pow(C.R,15,m)%m,-1,m)%m
N=(1+(H*pow(C.R,-1,m)%m)**2+2*f*pow(C.R,-1,m))%m
W=(N*N+C.R*Q*Q)%m
c=12*W*pow(C.A+1,-1,m)%m
D=C.B*c*c%m
L=(49*D-48)%m
assert L and L%p==0
s=[]
for x in range(p):
 q=(4-3*C.B*x*x)%p
 r=(4*(1+C.B*c*x)**2-3*C.B*(x+c)**2)%p
 if pow(q,41,p)==pow(r,41,p)==1:s.append((x,q,r))
assert s
print(json.dumps(dict(prime=p,order=o,chart_h=u,chart_shift=v,W=W,c=c,D=D,
   new_L_mod_p_square=L,new_L_over_p=L//p,first_smooth_square_pair=s[0],
   number_affine_smooth_square_pairs=len(s)),indent=2))
