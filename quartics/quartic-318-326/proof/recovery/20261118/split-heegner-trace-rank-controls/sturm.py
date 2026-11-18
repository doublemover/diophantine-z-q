"""Exact 128-coefficient modular identities, integral power series."""
T=128
def mul(a,b):return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(T+1)]
def pw(a,n):
 z=[1]+[0]*T
 while n:
  if n%2:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
def diff(a):return [i*v for i,v in enumerate(a)]
def sub(a,b):return [v-w for v,w in zip(a,b)]
def add(a,b):return [v+w for v,w in zip(a,b)]
f=[0,1]+[0]*(T-1)
for k in (2,4,6,12):
 for j in range(k,T+1,k):
  for m in range(T,j-1,-1): f[m]-=f[m-j]
g=[u*(-1 if k%4==3 else 1) for k,u in enumerate(f)]
A=[(u+v)//2 for u,v in zip(f,g)];C=[(v-u)//2 for u,v in zip(f,g)]
B=[f[j//2] if j%2==0 else 0 for j in range(T+1)]
W=sub(mul(A,diff(B)),mul(B,diff(A)))
assert mul(B,B)==mul(A,C)
assert mul(mul(W,W),mul(A,A))==add(add(pw(A,8),pw(B,8)),[14*u for u in mul(pw(A,4),pw(B,4))])
print('Checked level 48 index 96: weight 4 (bound 32) and weight 16 (bound 128); q through 128 inclusive.')
