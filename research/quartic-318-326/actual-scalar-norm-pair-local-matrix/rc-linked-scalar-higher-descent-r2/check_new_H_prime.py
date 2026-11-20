"""Verify new actual H-prime coordinates and eight residual norm labels."""
import contextlib,io,math,json,sys
from pathlib import Path
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/'rc-linked-scalar-specialization-r1'))
with contextlib.redirect_stdout(io.StringIO()):
    import check_actual_scalar_modular as E
B=E.C.B; C=E.C
S=json.loads((here.parent/'rc-linked-scalar-higher-descent-r1'/'EXACT-EIGHT-FIRST-CONIC-SEEDS.json').read_text())

def row(p):
    assert E.isprime(p)
    es=C.places(p); assert len(es)==2
    orders=[e.order() for e in es]
    vals=[[E.refine_split(p,i,o,e.d) for o,e in zip(orders,es)] for i in (C.h,C.shift)]
    u,v=vals; q=p*p
    H=u[0]*u[1]%q; I=v[0]*v[1]%q
    f=(u[0]**2+u[1]**2)*pow(2,-1,q)%q
    Q=I*pow(H*pow(C.R,15,q)%q,-1,q)%q
    N=(1+(H*pow(C.R,-1,q)%q)**2+2*f*pow(C.R,-1,q))%q
    W=(N*N+C.R*Q*Q)%q
    b=C.A*(W*pow(1+C.A,-1,q))**2%q
    delta=(1-b*pow(17,-1,q))%q
    assert delta%p==0
    tests=[(row['xi'],pow((-2*row['xi'])%p,(p-1)//2,p)==1) for row in S]
    return dict(prime=p,sqrt2=[e.d for e in es],orders=orders,chart_coeffs_mod_p_squared=vals,H_mod_p_squared=H,
        I_mod_p_squared=I,W_mod_p_squared=W,b_mod_p_squared=b,delta_mod_p_squared=delta,
        theta_factor=delta//p if delta else None,xi_test=tests,heegner_63839_split=(pow(-63839%p,(p-1)//2,p)==1))
P=[2470991] if len(sys.argv)==1 else [int(x) for x in sys.argv[1:]]
print(json.dumps([row(p) for p in P],indent=2))
