"""Finite tangent checkpoints; no claim of complete theta support."""
import hashlib,json
from math import gcd,prod
from pathlib import Path

root=Path(__file__).resolve().parents[3]
rc=root/'rc-native-helper-20261120/ct-original-constant15-nonnorm-retune-107-r1/EXACT-107-RETUNE-CONTROLS.json'
data=rc.read_bytes()
assert hashlib.sha256(data).hexdigest()=='4eeeda5471945a4793cc32c67a427ce85d45cc2f7fd27c375ff486aea20a50f3'
donor=json.loads(data)
assert donor['prime']==107 and donor['delta_mod_p2']==107
assert donor['conditional_phi_masks']==[0,255,16128,16383]
assert donor['conditional_psi_masks']==[0,4709,11674,16383]

B=204618888056724185
e=2952271997968816765
f=65029284442765
assert f==donor['known_opposite_class_e2']==prod((5,17,107,733,1489,6551))
x,y,z=31859917667562016618135,59323292900802,9995282212057
assert x*x-B*y*y==e*z*z and gcd(x,y,z)==1

def leg(t,p):
    t=pow(t%p,(p-1)//2,p)
    assert t in (0,1,p-1)
    return -1 if t==p-1 else t

def roots(t,p):
    return [r for r in range(p) if (r*r-t)%p==0]

assert B%8==1 and e%8==f%8==5 and f%3==1 and y%2==0 and not (x*z)%2==0
dyadic=dict(beta_mod8=B%8,e_mod8=e%8,f_mod8=f%8,
            L1_mod4=[(x-e*z*r-2*B*y)%4 for r in (1,3)],
            L2_mod4=[(x-e*z*r)%4 for r in (1,3)])
assert sorted(dyadic['L1_mod4'])==sorted(dyadic['L2_mod4'])==[0,2]

beta_rows=[]
for p in (5,17,1489):
    assert B%p==e%p==x%p==0 and (B//p)*(e//p)*z%p
    ys=roots(-(B//p)*pow(e//p,-1,p),p)
    assert len(ys)==2
    t=next(Y for Y in ys if (-(e//p)*z*Y-(B//p)*y)%p)
    a=(-(e//p)*z*t-(B//p)*y)%p
    b=9*a%p
    assert leg(a*b,p)==1
    beta_rows.append(dict(prime=p,Y_residue=t,Z_residue=9*t%p,first_stripped=a,second_stripped=b,sign=1))
p=733
assert B%p==0 and z%p and leg(e,p)==1
Y=next(Y for Y in roots(pow(e,-1,p),p) if (x-e*z*Y)%p)
a=(x-e*z*Y)%p
beta_rows.append(dict(prime=p,Y_residue=Y,Z_residue=Y,first_stripped=a,second_stripped=a,sign=1))

p=6551
c=2194
s=-pow(c,-1,p)%p
assert s*s%p==B%p and e%p==0
sm=(x-s*y)%p
assert sm==2382
a=s*sm%p; b=10*a%p
assert p%8==7 and leg(5,p)==leg(a*b,p)==1
v6551=dict(p=p,s=s,sigma_minus=sm,L1=a,L2=b,sign=1)

p=107
c=donor['c_mod_p2']
s=-pow(c,-1,p)%p
assert s*s%p==B%p and leg(5,p)==leg(e,p)==-1
assert (1-B*c*c)%p**2==p
vals=[]
for k in roots(5*pow(e,-1,p),p):
    X=9*s%p; Y=4*s*k%p
    L1=(x*X-e*z*Y-B*y)%p
    L2=((x+B*c*y)*X-9*B*(y+c*x))%p
    assert (X*X-e*Y*Y-B)%p==0 and (X*X-81*B)%p==0
    sign=leg(L1*L2,p)
    assert sign==1
    vals.append(dict(k=k,X=X,Y=Y,L1=L1,L2=L2,sign=sign))
assert [(a['L1'],a['L2']) for a in vals]==[(69,101),(25,101)]

K=[29,181,1346909,70850399941]
assert prod(K)==1+2448*B and gcd(f,prod(K))==1
poles=[(p,leg(f,p)) for p in K]
assert [s for _,s in poles]==[1,1,-1,1]
assert prod(s for _,s in poles)==-1
print(json.dumps(dict(f=f,dyadic=dyadic,beta_rows=beta_rows,theta_6551=v6551,
                      theta_107=dict(s=s,branches=vals),poles=poles,
                      admitted_cross_sign=-1),sort_keys=True,indent=2))
