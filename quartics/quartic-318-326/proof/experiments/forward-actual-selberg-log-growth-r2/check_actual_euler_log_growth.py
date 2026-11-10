#!/usr/bin/env python3
from fractions import Fraction as Q
import itertools,json,math
import sympy as s
import mpmath as m
m.mp.dps=90
c=dict(harmonic_euler=0,log_harmonic=0,exact_exclusion_sets=0,finite_positive_subproducts=0,actual_euler_factorizations=0,selected_growth_joins=0,uniform_prime_removals=0,optimizer_log_joins=0)
def le(a,b): assert a<=b+max(1,abs(a),abs(b))*m.mpf('1e-75'),(a,b)
def close(a,b): le(abs(a-b),m.mpf('1e-75'))
chi=lambda p:0 if p==2 else (1 if p%4==1 else -1)
ps=lambda N:list(map(int,s.primerange(2,N)))
for N in list(range(1,101))+[200,500,1000,10000]:
 H=sum((Q(1,n) for n in range(1,N)),Q(0));E=math.prod((Q(p,p-1) for p in ps(N)),start=Q(1))
 assert H<=E;c['harmonic_euler']+=1
 le(m.log(N),m.mpf(H.numerator)/H.denominator);c['log_harmonic']+=1
for F in [[2],[2,3],[2,3,5,7],[3,7,11],[2,3,5,7,11,13]]:
 for ch in [False,True]:
  f=lambda p:Q(p,p-(chi(p) if ch else 1))
  B=sum((math.prod((f(p) for p,b in zip(F,bits) if b),start=Q(1)) for bits in itertools.product([False,True],repeat=len(F))),Q(0))
  for bits in itertools.product([False,True],repeat=len(F)):
   assert math.prod((f(p) for p,b in zip(F,bits) if b),start=Q(1))<=1+B;c['finite_positive_subproducts']+=1
for kap,gs in [(1,[0,-1]),(318,[0,-318,1]),(326,[0,-326,2,5])]:
 k=len(gs);ex=2*abs(kap)*math.prod(abs(a-b) for a in gs for b in gs if a!=b)
 exc=set(map(int,s.primefactors(ex)));cut=16*(k+2);F=exc|set(ps(cut))
 # Explicit finite-subproduct upper majorant, product(1+f) equals powerset sum.
 U=1+m.fprod(1+m.mpf(p)/(p-1) for p in F)
 V=1+m.fprod(1+m.mpf(p)/(p-chi(p)) for p in F)
 # This is a conservative sanity constant derived from the actual boundary value.
 low=m.pi/4/(2*m.exp(2*m.log(4)*(1+1/m.log(2))+8*m.log(4)/m.log(2)))
 cc=low/V
 for N in [0,1,2,3,10,50,100,250,500,1000,2500]:
  allp=ps(N);sel=[p for p in allp if p not in exc and p>=cut]
  assert set(sel)==set(allp)-F;c['exact_exclusion_sets']+=1
  O=m.fprod(m.mpf(p)/(p-1) for p in sel);C=m.fprod(m.mpf(p)/(p-chi(p)) for p in sel)
  def density(p):
   x=chi(p);nz=p-x;nu0=p+(p-1)*x
   return Q((p-1)*nz*(2*nu0+(k-2)*nz)+nu0**2-1,p**4-1)
  dens={p:density(p) for p in sel}
  assert all(0<g<=Q(1,2) for g in dens.values())
  Ef=math.prod((1/(1-g) for g in dens.values()),start=Q(1));E=m.mpf(Ef.numerator)/Ef.denominator
  correction=m.fprod((1-m.mpf(g.numerator)/g.denominator)/((1-m.mpf(1)/p)**k*(1-m.mpf(chi(p))/p)**2) for p,g in dens.items())
  close(E,O**k*C**2/correction);c['actual_euler_factorizations']+=1
  for excluded in [0,2,67,97,1009]+sel[:2]:
   Er=math.prod((1/(1-g) for p,g in dens.items() if p!=excluded),start=Q(1))
   assert Ef/2<=Er;c['uniform_prime_removals']+=1
  if N>=2:
   le(m.log(N)/U,O);le(cc,C)
   W=1+correction # finite sanity upper; theorem obtains ONE uniform W from proved convergence.
   growth=cc**2/(W*U**k)
   le(growth*m.log(N)**k,E);c['selected_growth_joins']+=1
   dlow=E/4
   le(1/dlow,(4/growth)/m.log(N)**k);c['optimizer_log_joins']+=1
print(json.dumps({'status':'PASS','precision_digits':90,'checks':c,'scope':'Exact finite harmonic/product, original excluded-prime and density identities plus quantitative growth joins. The source proof, not finite tests, supplies uniform correction and character constants; no primitive-point or prime-pattern asymptotic inferred.'},sort_keys=True))
