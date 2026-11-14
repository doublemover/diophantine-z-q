"""Independent exact residue/count normalization checks, not a proof."""
import itertools,json,math
from fractions import Fraction as F

def count(k,q):
 a=[1]+[0]*(q-1)
 for c in (1,1,-1,-1,-k):
  b=[0]*q
  for x in range(q):b[c*x*x%q]+=1
  a=[sum(a[i]*b[(r-i)%q] for i in range(q)) for r in range(q)]
 assert sum(a)==q**5
 return a[0]
def check():
 out=[]
 for k in (318,326):
  for a,b in ((1,7),(2,3),(2,5),(3,4),(4,5),(5,9)):
   assert math.gcd(a,b)==1
   q=a*b
   assert len({(x%a,x%b) for x in range(q)})==q
   na,nb,nq=count(k,a),count(k,b),count(k,q)
   assert nq==na*nb
   assert F(nq,q**4)==F(na,a**4)*F(nb,b**4)
   out.append({'k':k,'a':a,'b':b,'count':nq})
 return {'status':'PASS exact finite regressions only','cases':out}
if __name__=='__main__':print(json.dumps(check(),indent=2))
