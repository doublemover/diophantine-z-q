#!/usr/bin/env python3
import itertools,json
import sympy as s
import mpmath as m
m.mp.dps=90
c=dict(complex_real_factors=0,positive_real_products=0,exact_prefix_tail_identities=0,fixed_exponent_tail_controls=0,actual_L_prefix_bounds=0,actual_prefix_shift_bounds=0,eventual_boundary_lowers=0,global_prefix_lowers=0)
def le(a,b):assert a<=b+max(1,abs(a),abs(b))*m.mpf('1e-75'),(a,b)
def close(a,b):le(abs(a-b),m.mpf('1e-75'))
chi=lambda p:0 if p==2 else (1 if p%4==1 else -1)
D=2*m.log(4)*(1+1/m.log(2));T=8*m.log(4)/m.log(2)
L1=m.dirichlet(1,[0,1,0,-1]);low=L1/(2*m.exp(D+T));assert low>0
def E(sig,ps):return m.fprod(1/(1-chi(p)*m.power(p,-sig)) for p in ps)
for sig in [m.mpf('1.001'),m.mpf('1.1'),m.mpf(2),m.mpf(4)]:
 for p0 in s.primerange(2,200):
  p=int(p0)
  a=1/(1-m.mpc(chi(p))*m.mpc(p)**(-m.mpc(sig)));b=1/(1-chi(p)*m.power(p,-sig))
  close(a,b);assert b>0;c['complex_real_factors']+=1
for N in [2,3,5,10,30,100,1000]:
 sig=1+1/m.log(N);pn=list(map(int,s.primerange(2,N)));pref=E(sig,pn);pref1=E(1,pn)
 assert pref>0 and pref1>0;c['positive_real_products']+=1
 for M in [N,N+1,2*N,10*N]:
  pm=list(map(int,s.primerange(2,M)));tail=[p for p in pm if p not in set(pn)]
  full=E(sig,pm);et=E(sig,tail)
  close(full,pref*et);c['exact_prefix_tail_identities']+=1
  le(et,m.exp(T));le(full,pref*m.exp(T));c['fixed_exponent_tail_controls']+=1
 L=m.dirichlet(sig,[0,1,0,-1]);le(abs(L),pref*m.exp(T));c['actual_L_prefix_bounds']+=1
 le(pref,pref1*m.exp(D));c['actual_prefix_shift_bounds']+=1
 le(low,pref1);c['eventual_boundary_lowers']+=1
N0=10
A=sum(1/E(1,list(map(int,s.primerange(2,n)))) for n in range(N0));K=1/low+1+A;cc=1/K
assert cc>0
for N in list(range(0,100))+[200,1000,10000,20000]:
 le(cc,E(1,list(map(int,s.primerange(2,N)))));c['global_prefix_lowers']+=1
print(json.dumps({'status':'PASS','precision_digits':90,'checks':c,'scope':'Same complex/positive-real Euler factors, exact fixed-N prefix/tail decomposition and boundary lower-bound sanity checks. The proof uses the genuine sigma>1 Euler limit with N fixed; no exchange of limits or sigma1 convergence claimed.'},sort_keys=True))
