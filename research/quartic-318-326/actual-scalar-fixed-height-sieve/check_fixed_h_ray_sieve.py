"""Exact square-residue height sieve for the two-chart discriminant at fixed h,J."""
import contextlib,io,math,json
from fractions import Fraction
with contextlib.redirect_stdout(io.StringIO()):
    import check_actual_scalar_modular as F
C=F.C
MAX=100000
P=[]
for p in range(11,501):
    if not F.isprime(p) or C.R*(C.A+1)*119%p==0:continue
    try:
        if p in C.SUP:
            b=C.A*pow(1+C.A,-1,p)**2%p
            row={'prime':p,'delta':(1-b*pow(17,-1,p))%p,'W':1}
        else:row=F.residue(p)
    except ValueError:continue
    P.append(row)

def build(row):
    p=row['prime'];D=(1-row['delta'])%p
    cube=[x*x%p for x in range(p)]
    sq=set(cube)
    Dterm=(82*D-18)%p; det=9*row['delta']**2%p; b=C.B%p
    table=[];pop=0
    periodic=((1<<(p*((MAX//p)+1)))-1)//((1<<p)-1)
    near=((1<<(MAX+1))-1)^1
    for d2 in cube:
        d4=d2*d2%p
        pattern=sum(1<<a for a,a2 in enumerate(cube) if b*(9*a2*a2+Dterm*a2*d2+det*d4)%p in sq)
        pop+=pattern.bit_count()
        table.append((pattern*periodic)&near)
    return Fraction(pop,p**2),p,table
masks=sorted(map(build,P))
survivors=[]
passes=[0]*(len(masks)+1)
for d in range(1,MAX+1):
    m=(1<<(MAX+1))-2;passes[0]+=m.bit_count()
    for j,(_,p,T) in enumerate(masks,1):
        m &= T[d%p]
        if not m:break
        passes[j]+=m.bit_count()
    if m:
        while m:
            l=m&-m;n=l.bit_length()-1;m-=l
            if math.gcd(n,d)==1:survivors.append((n,d))
assert not survivors
order=[p for _,p,_ in masks]
print(json.dumps({'bound':MAX,'modular_rows':P,'processed_prime_order':order,
    'initial_signed_nonzero_ratio_rows_before_gcd':2*passes[0],
    'unsigned_survivor_counts_before_gcd':passes,
    'primitive_positive_survivors':survivors},indent=2))
