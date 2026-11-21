from itertools import product
from random import Random
from fractions import Fraction
from math import prod
rnd=Random(318326)
checked=exact=0
for _ in range(5600):
 a,t,b,s= rnd.randrange(4),rnd.randrange(3),rnd.randrange(1,4),rnd.randrange(1,4)
 J,M,n,q=[rnd.randrange(1,9) for _ in range(4)]
 A=[[rnd.randrange(-8,9) for _ in range(s)] for _ in range(b)]
 g=[[rnd.randrange(J) for _ in range(2)] for _ in range(a)]
 h=[[rnd.randrange(M) for _ in range(s)] for _ in range(t)]
 l=[[[rnd.randrange(2*M+1) for _ in range(2)] for _ in range(b)] for _ in range(t)]
 bits=[rnd.randrange(2) for _ in range(a+t*b)]
 xs=rnd.randrange(n)
 coords=[('g',i,e) for e in (0,1) for i in range(a)]+[p for r in range(t) for p in
   [('h',r,k) for k in range(s)]+[('l',r,j,e) for j in range(b) for e in (0,1)]]
 rnd.shuffle(coords)
 vals={p:g[p[1]][p[2]] if p[0]=='g' else (h[p[1]][p[2]]+1 if p[0]=='h' else l[p[1]][p[2]][p[3]]-M) for p in coords}
 lhs=q*sum(bits[i]*(g[i][1]-g[i][0]) for i in range(a))+sum(
   bits[a+r*b+j]*sum(A[j][k]*(h[r][k]+1) for k in range(s))*(l[r][j][1]-l[r][j][0])
   for r in range(t) for j in range(b))
 rhs=q*sum(bits[i]*(vals['g',i,1]-vals['g',i,0]) for i in range(a))+sum(
   bits[a+r*b+j]*sum(A[j][k]*vals['h',r,k] for k in range(s))*(vals['l',r,j,1]-vals['l',r,j,0])
   for r in range(t) for j in range(b))
 assert lhs==rhs and (xs+lhs)%n==(xs+rhs)%n
 widths=[J if p[0]=='g' else M if p[0]=='h' else 2*M+1 for p in coords]
 assert prod(widths)==J**(2*a)*(M**s*(2*M+1)**(2*b))**t
 checked+=1
for a,t,b,s,J,M in [(0,0,1,1,1,1),(1,0,2,1,2,1),(0,1,2,1,1,2),(0,2,2,1,1,1),(1,1,2,1,2,1)]:
 n,q=7,3
 widths=[J]*(2*a)+([M]*s+[2*M+1]*(2*b))*t
 D=J**(2*a)*(M**s*(2*M+1)**(2*b))**t
 orders=list(product(*(range(w) for w in widths)))
 assert len(orders)==D
 sums=[0,0]
 for v in orders:
  left=lambda i: v[2*i+1]-v[2*i]
  base=lambda r: 2*a+r*(s+2*b)
  slope=lambda r,j: sum((j-2)*(k+1)*(1+v[base(r)+k]) for k in range(s))
  for x in range(n):
   for k in range(2):
    res=1
    for w in product((0,1),repeat=a+t*b):
     h=q*sum(w[i]*(left(i) if k==0 else (v[2*i+1]+123)-(v[2*i]+123)) for i in range(a))
     h+=sum(w[a+r*b+j]*slope(r,j)*((v[base(r)+s+2*j+1]-k*M)-(v[base(r)+s+2*j]-k*M))
             for r in range(t) for j in range(b))
     res*=((x+h)%n)-3
    sums[k]+=res
 assert Fraction(sums[0],n*D)==Fraction(sums[1],n*D)
 exact+=n*D
print('quantized-shift-and-card controls',checked,'exact signed same-x tuples',exact)
