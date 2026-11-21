"""Actual a=0 scalar retuning at one fixed q; preserve the four old theta units."""
from pathlib import Path
import contextlib,io,runpy,json,math
home=Path(__file__).resolve().parent.parent
with contextlib.redirect_stdout(io.StringIO()):
 s=runpy.run_path(str(home/'rc-linked-scalar-specialization-r1/select_scalar_specialization.py'))
q=1041427
assert all(q%p for p in range(2,math.isqrt(q)+1))
R,B,M,K=s['R'],s['B'],s['A']+1,s['B0']
h0=s['h']; i0=s['shift']; m0=i0//h0
assert i0==h0*m0

def chi(x,p):
 bit=pow(x%p,(p-1)//2,p)
 assert bit in (1,p-1)
 return 1 if bit==1 else -1

def crt(a,m,b,n):
 g=math.gcd(m,n); assert (b-a)%g==0
 j=((b-a)//g)*pow(m//g,-1,n//g)%(n//g)
 out=a+m*j
 assert out%m==a%m and out%n==b%n
 return out%math.lcm(m,n),math.lcm(m,n)

rows_s=json.loads((home/'rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.json').read_text())
rows_l=json.loads((home/'rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json').read_text())
small=rows_s[0]; assert small['prime']==6551
here=[(6551,small['orders'],small['precision_two']['delta']),
      *[(r['prime'],r['orders'],r['delta_mod_p_squared']) for r in rows_l]]
T=math.lcm(*(p*p*math.lcm(*orders) for p,orders,ds in here))
assert T%q
theta=[(131,82)]+[(p,delta//p) for p,orders,delta in here]
assert all(0<u<p for p,u in theta)
Es=s['places'](q);assert len(Es)==1
n=Es[0].order()
assert n==347142 and Es[0].nsmul(n) is None and all(Es[0].nsmul(n//p) is not None for p in s['factors'](n))
Mh=math.lcm(h0,q*n)
head,stride=crt(0,Mh,h0,T)
for j in range(1000):
 h=head+stride*j
 if h<2:continue
 ok,intv=s['real_margin'](h)
 if ok:break
else:raise ArithmeticError("real margin not found in explicit control")
assert h%Mh==0 and h%T==h0%T
old_depth=math.prod(p**((15*s['vp'](R,p)+2)//2) for p in s['SUP'])
L=math.lcm(K//math.gcd(K,h),old_depth,T//math.gcd(T,h0))
assert math.gcd(L,q)==1
# This residue is compatible with both old divisibilities, since h0|h.
assert m0%old_depth==0 and (h*m0)%K==0
m,ms=crt(m0%L,L,7,q*q)
assert m%old_depth==0 and m%ms==m and m>0
i=h*m;assert i%K==0 and i%T==i0%T
# The older endpoint regularity is checked at the two exact branch residues.
# Congruence mod p^2*order then preserves the regular integral chart mod p^2.
retained_regular = []
for p, old_orders, delta_old in here:
  roots=[r for r in range(p) if (r*r-2)%p==0] if p==6551 else next(z['sqrt2'] for z in rows_l if z['prime']==p)
  assert len(roots)==2 and roots[0]+roots[1]==p and all(r*r%p==2 for r in roots)
  rr=[]
  for root,nold in zip(roots,old_orders):
    e=s['E'](p,root)
    assert e.nsmul(nold) is None
    P=e.nsmul(h0%nold); Q=e.nsmul(i0%nold)
    assert P is not None and P[1]%p and (P[0]**2+e.D)%p
    assert Q is None or (Q[0]**2+e.D)%p
    assert h%(p*p*nold)==h0%(p*p*nold) and i%(p*p*nold)==i0%(p*p*nold)
    rr.append([root,P,Q])
  retained_regular.append([p,rr])
J=i//K
mod=q*q
W=(1+pow(m,4,mod)*pow(R,-29,mod))%mod
c=12*W*pow(M,-1,mod)%mod
delta=(1-B*c*c)%mod
Arad=(1-21060**2*delta)%mod
assert c%q and (1-49*delta)%q and chi(delta,q)==-1 and chi(Arad,q)==1
# Preserve the scalar 53 branch by the old W ≡1 witness.
cs=12*pow(M,-1,53)%53; ds=(1-B*cs*cs)%53
assert ds==17 and chi(1-21060**2*ds,53)==-1
bs=[5,11,17,163,661,733,1489,1861]
assert B==math.prod(bs) and all(chi(q,p)==-1 for p in bs)
assert q%24==19 and chi(q,53)==-1 and chi(1-108**2,q)==1
assert (1-108**2)==-107*109 and chi(1-108**2,17)==1 and chi(1-108**2,53)==-1
assert chi(2,q)==-1 and all(x%q for x in (1,2,5))
ps=[p for p,u in theta]; d=[int(chi(u,p)<0) for p,u in theta]; x=[int(chi(q,p)<0) for p in ps]
assert d==[1,0,0,0] and x==[0,1,0,0]
H=[[int(chi(r,p)<0) if j!=i else d[i]^x[i] for j,r in enumerate(ps)] for i,p in enumerate(ps)]
bits=[[int(chi(r,p)<0) if i!=j else 0 for j,r in enumerate(ps)] for i,p in enumerate(ps)]
def kernel(rows):
  return [v for v in range(1<<len(rows))
          if all(sum(r[j]*((v>>j)&1) for j in range(len(rows)))%2==0 for r in rows)]
assert kernel(H)==[0]
b=[d[i]^(sum(bits[i])%2) for i in range(4)]
assert b==[0,0,1,0] # if exactly one hidden prime, it is 13 mod24 and reciprocity is symmetric here
hidden=int(chi(delta,q)<0)^(sum(x)%2)
assert hidden==0
H5=[r+[bb] for r,bb in zip(H,b)]+[b+[(sum(b)%2)^hidden]]
assert kernel(H5)==[0]  # conditional only: assumes precisely one unseen theta prime
F5=s['places'](5)[0]
assert h%5==i%5==0 and F5.order()==5
guards=[F5.recip(-2*l)[0] for l in (3723,1,-1,1)]
assert guards==[4,1,1,1]
cap=1<<(s['Ball'].precision-64)
left=intv.lo//cap
right=-((-intv.hi)//cap)
assert left*right>0 and 100*min(abs(left),abs(right))>2**64
print(json.dumps({'q':q,'q_order':n,'h_CRT_base':str(head),'h_CRT_step':str(stride),'h':str(h),'h_real_j':j,'J':str(J),
'norm_interval_div_2pow64':[left,right],'guards_mod5':guards,'retained_scalar_modulus':str(T),
'old_and_new_h_same_modulus':str(h%T),'old_and_new_i_same_modulus':str(i%T),
'retained_theta_first_units':theta,'retained_regular_mod_p_elliptic_branches':retained_regular,'q2_W_c_delta_K_radicand':[W,c,delta,Arad],
'q_minus_Gaussian':{'A_B':[1,1],'norm':2,'neighbor_norms':[1,5]},
'scalar_q_beta_symbols':[-1]*8,'q_theta_bits':x,
'known_theta_principal_block':H,
'only_if_hidden_prime_count_is_one':{'extra_bit':hidden,'principal_block':H5}},indent=2))
