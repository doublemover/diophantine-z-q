#!/usr/bin/env python3
"""Exact polynomial verification plus finite-field sanity, not a Lean run."""
import sympy as S
x,y=S.symbols('x y')
r,s,t,u,R,T0,T,U=S.symbols('r s t u R S T U')
conic=x*x+210*y*y-5
def matrix(q):
 r,s,t,u=q
 return S.Matrix([[r+x*t-210*y*u,-210*s+210*y*t+210*x*u],
                  [s+y*t+x*u,r-x*t+210*y*u]])
def multiply(a,b):
 r,s,t,u=a;R,Ss,T,U=b
 return [r*R-210*s*Ss+5*t*T+1050*u*U,
         r*Ss+s*R-5*t*U+5*u*T,
         r*T+t*R-210*s*U+210*u*Ss,
         r*U+u*R+s*T-t*Ss]
def inverse(M):
 A,B,C,D=list(M)
 return [(A+D)/2,(C-B/210)/2,
         (x*(A-D)+210*y*(C+B/210))/10,
         (-y*(A-D)+x*(C+B/210))/10]
a=[r,s,t,u];b=[R,T0,T,U]
res=matrix(multiply(a,b))-matrix(a)*matrix(b)
coeffs=[-(t*T+210*u*U),210*(u*T-t*U),t*U-u*T,-(t*T+210*u*U)]
assert all(S.expand(v-c*conic)==0 for v,c in zip(res,coeffs))
assert all(S.expand(v-w-c*conic)==0 for v,w,c in zip(inverse(matrix(a)),a,[0,0,t/5,u/5]))
A,B,C,D=S.symbols('A B C D');M=S.Matrix([[A,B],[C,D]])
coeffs=[(A-D)/10,(B+210*C)/10,(B+210*C)/2100,-(A-D)/10]
assert all(S.expand(v-c*conic)==0 for v,c in zip(matrix(inverse(M))-M,coeffs))
N=r*r+210*s*s-5*t*t-1050*u*u
assert S.expand(matrix(a).det()-N+(t*t+210*u*u)*conic)==0
I=matrix([0,1,0,0]);J=matrix([0,0,1,0])
assert I*I==-210*S.eye(2)
assert I*J+J*I==S.zeros(2)
assert J*J==(conic+5)*S.eye(2)
count=0
for p in S.primerange(2,250):
 if 210%p==0:continue
 solutions=[(i,j) for i in range(p) for j in range(p) if (i*i+210*j*j-5)%p==0]
 assert solutions and all((2*i)%p or (420*j)%p for i,j in solutions)
 count+=1
print('PASS original quaternion multiplication, both complete matrix inverse identities, scalar/norm convention and generator relations.')
print(f'PASS exact finite conic/smoothness checks at all {count} primes below250 outside210. The all-prime statement uses the pinned finite-field theorem and actual Hensel lemma, not this bounded check.')
