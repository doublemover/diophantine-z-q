from math import prod,isqrt
from itertools import combinations
import json
L=[(7446,661),(7446,1861),(29784,7445),(476544,119479)]
src=[4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344]
def factor(n):
 out={};j=2
 while j*j<=n:
  while n%j==0:out[j]=out.get(j,0)+1;n//=j
  j+=1
 if n>1:out[n]=1
 return out
def v(n,p):
 z=0
 while n%p==0:n//=p;z+=1
 return z
poly=[4]
for slope,intercept in L:
 poly=[intercept*(poly[i] if i<len(poly) else 0)+slope*(poly[i-1] if i else 0) for i in range(len(poly)+1)]
assert poly==src
det={};pairs=[]
for i,j in combinations(range(4),2):
 a,c=L[i];b,d=L[j];f=factor(abs(a*d-b*c));det['UV WZ'.replace(' ','')[i]+'UV WZ'.replace(' ','')[j]]=f
 p=[q for q in f if q%4==3 and q!=3];pairs.append(p)
assert pairs==[[],[],[7],[],[],[359]]
R11={a*(a+1)%11 for a in range(11)};assert R11=={0,1,2,6,8,9} and all((x*t+y)%11 for t in R11 for x,y in L[2:])
assert 2*7446==4*3723 and 2*661==3723-7**4 and 3723%7==6 and 6 not in {a*a%7 for a in range(7)}
controls=[]
for a in [-123,-1,0,1,2,3,7,24,73,122,171]:
 t=a*(a+1);u,v0,w,z=[x*t+y for x,y in L]
 assert v(u,7)==min(2*v(2*a+1,7),4) and sum(x*t**i for i,x in enumerate(src))==4*u*v0*w*z
 N=17*11*u*v0*w*z;assert N%4==1
 qs=[p for p in set(factor(w))|set(factor(z)) if p%4==3 and v(N,p)%2]
 assert qs;controls.append(dict(a=a,odd_bad_witness_in_WZ=min(qs),v7_U=v(u,7)))
print(json.dumps(dict(source_coefficients=poly,determinants=det,local_t_mod11=sorted(R11),controls=controls),indent=2))
