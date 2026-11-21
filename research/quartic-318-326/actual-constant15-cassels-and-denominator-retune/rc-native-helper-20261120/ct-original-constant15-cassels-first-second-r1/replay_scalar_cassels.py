"""Exact known-source support bits, conditional one-hidden rows, and rank-one toy."""
from itertools import product
from math import prod,isqrt
from pathlib import Path
from fractions import Fraction as Q
import json
p=Path(__file__).resolve().parent.parent
inp=p/'ct-original-scalar-mestre-marked-selmer-r1'/'EXACT-MARKED-SELMER-ROWS.json'
old=p/'ct-original-constant15-transpose-selmer-r1'/'EXACT-TRANSPOSE-SEL-CONTROLS.json'
S=json.loads(inp.read_text()); F=json.loads(old.read_text())
B=(5,11,17,163,661,733,1489,1861); V=(131,6551,2470991,16782959)
P=B+V; beta=prod(B)
D=dict(zip(P,S['true_d_stripped_bits']))
def ell(a,p):
 assert a%p
 v=pow(a%p,(p-1)//2,p);assert v in (1,p-1)
 return int(v==p-1)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%2
def bitvec(x):return sum(int(u)<<i for i,u in enumerate(x))
def mat(P):
 r=[ell(-1,p) for p in P];t=[ell(p,3) for p in P];m=len(P)
 M=[[0 if p==q else ell(q,p) for q in P] for p in P]
 for i in range(m):M[i][i]=sum(M[i])%2
 return [[M[i][j]^((t[i]^r[i])*r[j]) for j in range(m)] for i in range(m)],r,t
def local5(x):
 v=0
 while x%5==0:x//=5;v+=1
 return v%2,ell(x,5)
def psi(e,f,P):
 r=((e<0)*(f<0)+(e%4==3)*(f%4==3)+sum((p%4==3) for p in P if e%p==f%p==0))%2
 return r
def phi(e,f,P,d):
 v=sum(ell(-5,p) if p!=5 else ell(d//5,5) for p in P if e%p==f%p==0)%2
 if 5 not in P and ell(d,5):v^=ell(e,5)*ell(f,5)
 return v
for T in F['examples']:
 d,P0=T['d'],T['prime_support']
 augmented=T['augmentation']
 for e in T['psi']:
  for f in T['psi']:
   a,b=local5(e);c,u=local5(f)
   assert psi(e,f,P0)==((a*u+b*c)%2 if augmented else 0)
 for e in T['phi']:
  assert phi(e,e,P0,d)==phi(d,e,P0,d)==0

mark=[p for p in B if (ell(-5,p) if p!=5 else D[p])]
assert mark==[5,11,17,733]
ag={p:D[p]^sum(ell(q,p) for q in P if q!=p)%2 for p in P}
assert [ag[p] for p in P]==S['conditional_one_unseen']['aggregate_bits']
def analyze(N):
 Qs=P if N==13 else P[:N]
 H=prod(V)
 r=[ell(-1,p) for p in Qs]+([0] if N==13 else [])
 t=[ell(p,3) for p in Qs]+([0] if N==13 else [])
 Z=[[D[p] if p==q else ell(q,p) for q in Qs] + ([ag[p]] if N==13 else []) for p in P]
 if N==13:Z.append([ag[q] for q in Qs]+[sum(ag.values())%2])
 ZZ=[[v^((ell(3,p) if i<len(P) else 0)*r[j]) for j,v in enumerate(row)] for i,(p,row) in enumerate(zip(P+('?',),Z))]
 assert len(ZZ)==(13 if N==13 else 12)
 K=[a for a in product((0,1),repeat=N) if not any(dot(row,a) for row in ZZ)]
 assert all(dot(a,[int(p in mark) for p in B])==0 for a in K)
 return [bitvec(a) for a in K],ZZ,r,t
ks,_,_,_=analyze(8);ks12,_,_,_=analyze(12);ks13,A,r,t=analyze(13)
assert sorted(ks)==sorted(ks12)==[0,255] and sorted(ks13)==[0,255,7936,8191]
At=list(zip(*A))
Kpsi=[a for a in product((0,1),repeat=13) if not any(dot(row,a) for row in At)]
assert sorted(bitvec(a) for a in Kpsi)==[0,1863,6328,8191]
a=tuple((1863>>i)&1 for i in range(13));assert dot(t,a)==0 and not a[-1]
e=prod(p for p,x in zip(P,a) if x)
assert e==2952271997968816765 and e%4==1 and e%3==1
fixed=(29,181,1346909,70850399941)
fixed_bits=[sum(ell(q,p) for p in P if e%p==0)%2 for q in fixed]
assert fixed_bits==[0,1,0,1]
theta_overlap=[p for p in V if e%p==0]
assert theta_overlap==[131,6551,2470991] and sum(ell(2,p) for p in theta_overlap)%2==1

# Positive original-type numerical control only; the actual source has not changed.
B1=17*2857; t1=Q(60,119009); u=B1*t1*t1
c=10*t1/(1+9*u); delta=1-B1*c*c; b=17*B1*c*c
q=(13,163,199,13988293681)
def prime(a):return a>1 and all(a%k for k in range(2,isqrt(a)+1))
assert all(prime(a) for a in q)
theta=prod(q); d=B1*theta
assert theta==(119009**2-B1*60**2)*(119009**2-81*B1*60**2)
assert delta==theta/(Q(119009**2+9*B1*60**2)**2)
assert 0<b<17 and 0<u<Q(1,81) and d==286488990122412554009
assert d%24==17 and theta%24==1 and isqrt(b.denominator)**2==b.denominator
def vp(a,p):
 def v(n):
  k=0
  while n%p==0:k+=1;n//=p
  return k
 return v(a.numerator)-v(a.denominator)
assert [vp(b,p) for p in (2,3,17)]==[6,2,2] and B1//17==2857
for p in (2,3,17):
 u0=b/Q(p**vp(b,p))
 m=8 if p==2 else p
 w=u0.numerator*pow(u0.denominator,-1,m)%m
 assert (w==1 if p==2 else ell(w,p)==0)
assert all(ell(B1,p)==0 for p in q) and all(ell(theta,p)==0 for p in (17,2857))
V1=(1-u)*(1-81*u)/(1+9*u)
assert V1*V1==delta*(1-u)*(1-81*u)
A1,r1,tv=mat((17,2857,*q));l=[ell(p,5) for p in (17,2857,*q)]
A1.append([x^y for x,y in zip(r1,l)])
K1=[a for a in product((0,1),repeat=6) if not any(dot(row,a) for row in A1)]
Kt=[a for a in product((0,1),repeat=7) if not any(dot(row,a) for row in zip(*A1))]
assert (len(K1),len(Kt))==(4,8) and d%5==4
ps=[(-1)**(dot(tv,a)^a[-1])*5**a[-1]*prod(p for p,x in zip((17,2857,*q),a) if x) for a in Kt]
assert -10595 in ps and -17 in ps
assert psi(-10595,-17,(17,2857,*q))==1
assert local5(-10595)==(1,0) and local5(-17)==(0,1)
print(json.dumps(dict(actual_beta_prime_obstruction_bits=mark,visible_only_rational_class_candidates=[1,beta],
                      actual_support_mask_counts=[len(ks),len(ks12)],
                      one_hidden_conditional_phi_masks=sorted(ks13),one_hidden_conditional_psi_test=e,
                      test_theta_overlap=theta_overlap,fixed_odd_denominator_bits=fixed_bits,
                      second_bit_formula="negative times Jacobi(D_exc/e); actual Jacobi value uncomputed",
                      numerical_ready_rank_one_toy={"d":d,"beta":B1,"theta":theta,"t":str(t1),"b":str(b),
                       "phi_dimension":2,"psi_dimension":3,"psi_nonzero_pair":[-10595,-17],
                       "literal_source":False}),indent=2,sort_keys=True))
