#!/usr/bin/env python3
"""Original split D=-43: exact arithmetic only, no modularity/period claims."""
from fractions import Fraction as Q
from itertools import permutations, product
from json import dumps

T=Q(10976,43); q=T/32; z=Q(-2); u,v=q.numerator,q.denominator
r=[392,240,11760,735]
assert [Q(-43)*Q(s,43)**2 for s in r]==[-14*T,-6*(T-32),42*(T-76832),-21*(T+343)]
assert 49*Q(r[1],r[0])==30 and 8*Q(r[3],r[0])==15
assert Q(-30,15)==z
assert (u,v)==(343,43)
assert [u,v,u-v,u-2401*v,32*u+343*v]==[343,43,300,-102900,25725]

# Positive endpoint fold, from the paper's actual half-turn labels.
# Basis is 1,mu,j,mu*j; monomial exponents are the two binary bits.
def quat_mul(a,b):
 out=[Q(0)]*4
 for i,j in product(range(4),repeat=2):
  x,y=i%2,i//2; z,w=j%2,j//2
  out[i^j]+=a[i]*b[j]*(-1)**(y*z)*(-210)**(x*z)*5**(y*w)
 return out
mu=[0,1,0,0];j=[0,0,1,0]
H30=[0,1,6,0]; H105=[0,Q(7,2),21,Q(-1,2)]; H70=[0,Q(5,2),14,Q(-1,2)]
p=quat_mul(quat_mul(quat_mul(H70,H105),H30),mu)
s=[1,-1,1,-1]  # diag(-1,1) conjugation on 1,mu,j,mu*j
fold=quat_mul(mu,[x*y for x,y in zip(s,p,strict=True)])
assert [x/210**2 for x in fold]==[Q(5,2),0,Q(-1,2),0]
assert quat_mul([Q(-1,2),0,Q(1,2),0],j)==[Q(5,2),0,Q(-1,2),0]

# Literal arithmetic left operator rows on O_F^2, basis (1,w) in each factor.
def matrix(f): return [[f(i,j) for j in range(4)] for i in range(4)]
def mv(M,x): return [sum(m*t for m,t in zip(r,x,strict=True)) for r in M]
def mm(M,N): return matrix(lambda i,j:sum(M[i][k]*N[k][j] for k in range(4)))
def det_cols(C):
 return sum((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
            *C[0][p[0]]*C[1][p[1]]*C[2][p[2]]*C[3][p[3]] for p in permutations(range(4)))
Id=matrix(lambda i,j:int(i==j))
f=[[0,0,1,0],[0,0,0,1],[1,0,1,0],[0,1,0,1]]
J=matrix(lambda i,j:2*f[i][j]-Id[i][j])
g=[[-5,0,-2,11],[0,-5,-1,-3],[-3,-11,5,0],[1,-2,0,5]]  # actual folded -g_raw
assert mm(f,f)==matrix(lambda i,j:f[i][j]+Id[i][j])
assert mm(g,g)==matrix(lambda i,j:42*Id[i][j])
assert mm(g,f)==mm(matrix(lambda i,j:Id[i][j]-f[i][j]),g)
assert mm(mm(g,J),mm(g,J))==matrix(lambda i,j:-210*Id[i][j])
ell=mv(matrix(lambda i,j:f[i][j]-Id[i][j]),[-1,0,-1,0])
assert ell==[0,0,-1,0]
orb=[ell,mv(mm(g,J),ell),mv(f,ell),mv(mm(g,f),ell)]
assert det_cols(orb)==-1

# The actual elliptic generalized Weierstrass equation.
a1,a2,a3,a4,a6=0,0,1,-860,9707
b2=a1*a1+4*a2; b4=2*a4+a1*a3; b6=a3*a3+4*a6
c4=b2*b2-24*b4; c6=-b2**3+36*b2*b4-216*b6
Delta=Q(c4**3-c6**2,1728); j0=Q(c4**3)/Delta
assert (c4,c6,Delta,j0)==(41280,-8387064,-43**3,-884736000)
p3=[-a4*a4,3*b6,3*b4,b2,3]  # ascending coefficients
assert p3==[-739600,116487,-5160,0,3]

def mod_rem(f,g,p):
 f=[c%p for c in f]
 for i in range(len(f)-len(g),-1,-1):
  a=f[i+len(g)-1]*pow(g[-1],-1,p)%p
  for j,c in enumerate(g): f[i+j]=(f[i+j]-a*c)%p
 return f[:len(g)-1]
f11=[c*pow(3,-1,11)%11 for c in p3]
assert f11==[6,10,7,0,1]
assert (-43)%11==1
assert all(any(mod_rem(f11,[h,1],11)) for h in range(11))
assert all(any(mod_rem(f11,[a,b,1],11)) for a,b in product(range(11),repeat=2))
assert (-43)%3==2
# Good reduction at 43 after *literal* marked [3] produces the scaling.
assert (-400)%43 and (3*20**2-120*20-400)%43
assert (9707*4+1)==21*43**2

def val(poly,x): return sum(Q(a)*x**i for i,a in enumerate(poly))
def der(poly,x): return val([i*a for i,a in enumerate(poly) if i],x)
F=[43,-600,986,600,43]; G=[1,-14,23,14,1]; A=[-2,11,-52,25,2]
N=[10976,0,21952,0,10976]
F0,G0,A0,N0=(val(p,z) for p in (F,G,A,N))
Tz=Q(der(N,z)*F0-N0*der(F,z),F0**2)
assert (F0,G0,A0,N0,Tz)==(1075,25,-400,274400,Q(-1317120,1849))
assert N0/F0==T and N0-76832*F0==-3292800*G0
B0=Q(2)*A0**3/j0
kappa=Q(c4)/A0
assert c4**2/kappa**2==A0**2
assert c6**2/kappa**3==A0**3-864*B0
raw=-Q(12600)/(F0*G0)/kappa/Tz**2
primitive=raw/210
D=T*(T-32)*(T-76832)*(T+343)
p0=205800/(D*primitive); p1=Q(25725,4)*T/(D*primitive)
K=1/(D*raw)
assert raw==Q(1849,206524416000)
assert primitive==Q(1849,43370127360000)
assert (p0,p1,K)==(-1849,-14749,Q(-1849,43218000))
assert p0%2==1 and p1%2==1 and p0*Q(1,43)==-43 and p1*Q(1,43)==-343
# Irrational scalar exclusion independent of the product classification.
assert T/119136 == Q(343,3*17*43*73)
assert Q(2)*Q(1,200)/(1-Q(1,200))**2<Q(1,90)
assert Q(5,2)**7>343
print(dumps({'split_T':str(T),'q':str(q),'marked_radical_magnitudes_over_sqrt_D':r,
 'fold':[str(x/210**2) for x in fold],'held_primitive_lattice_generator':ell,
 'actual_signed_orbit_columns':orb,'elliptic_Weierstrass':[a1,a2,a3,a4,a6],
 'c4':c4,'c6':c6,'Delta':str(Delta),'j':str(j0),'psi3_mod11_ascending':f11,
 'dT_dz':str(Tz),'raw_Psi_dT_squared':str(raw),'primitive_Phi_dT_squared':str(primitive),
 'Hodge_coefficient_S0_S1':[str(p0),str(p1)],'arch_kappa_eta0':str(K)},indent=2))
