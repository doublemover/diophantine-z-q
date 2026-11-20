"""Exact p83 coefficients and known-support local certificate for the split dual."""
import json
from math import prod
from pathlib import Path
j=json.loads((Path(__file__).resolve().parent.parent/'rc-linked-scalar-norm-pair-r1'/
 'ACTUAL-ALT-PRIME-83.json').read_text())
B=(5,11,17,163,661,733,1489,1861)
H=(131,6551,2470991,16782959)
beta=prod(B)
p=83;m=p*p;c=j['c']
D=beta*c*c%m
F=(49*D-48)%m
A=beta*(25*D-24)%m
K=12*beta*(1-D)%m
A1=(-2*A)%m
B1=(A*A-4*K*K)%m
assert j['D']==D and F==81*p and B1==7*p
assert B1==beta*beta*D*F % m
assert (-A*pow(2,-1,p))%p==56 and A1%p==58
def char(x,p):
    assert x%p
    return 1 if pow(x%p,(p-1)//2,p)==1 else -1
assert (9**2-5*(25+A1*5+B1))%p==0 and char(5,p)==-1
assert char(B1//p,p)==1
base=-6*beta*p
M={str(q):char(166,q) for q in B}
M.update({str(q):char(base,q) for q in H})
M['7']=char(base,7)
M['83']=char(beta*(F//p),p)*char(base//p,p)
assert M=={'5':1,'11':1,'17':1,'163':-1,'661':1,'733':-1,
      '1489':1,'1861':1,'131':-1,'6551':1,'2470991':1,'16782959':1,'7':-1,'83':1}
k0=(5,11,163,733,1489,6551,2470991)
assert prod(k0)==158389989243518750905 and prod(M[str(q)] for q in k0)==1
assert (base//2)%8==7 and (base//3)%3==1

def loc(x,p):
    v=0
    while x%p==0:x//=p;v^=1
    return (v,x%8 if p==2 else char(x,p))
gens=(-1,2,3,*B,83)
alive=[prod(q for i,q in enumerate(gens) if bits>>i&1) for bits in range(1<<len(gens))]
steps=[len(alive)]
for q in (2,3,*B,*H):
    if q==2: target={(0,1),(0,5),(1,3),(1,7)}
    elif q==3:target={(0,1),(1,1)}
    elif q in B:target={(0,1),loc(-3*beta,q)}
    else:target={(0,1)}
    alive=[x for x in alive if loc(x,q) in target]
    steps.append(len(alive))
assert alive==[1]
print(json.dumps(dict(prime83=dict(D=D,F=F,original_A=A,original_node=56,
    dual_A_mod_prime=58,dual_B_over_prime_mod_prime=B1//p,
    dual_nonsquare_unit_witness=[5,9]),
    visible_torsion_factor=base,hidden_M_unit_characters=M,
    hidden_M_mod24=1,kernel_character=prod(M[str(q)] for q in k0),
    local_dual_filter_order=[2,3,*B,*H],local_dual_filter_counts=steps,
    viable_classes_on_known_only_support=alive),indent=2))
