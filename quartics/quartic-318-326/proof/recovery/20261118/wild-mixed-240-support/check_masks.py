from itertools import product
from collections import Counter
def cls(c): return (int(c<0))|(2*int(abs(c)==2))
def run():
 counts=Counter()
 for qs in product((1,-1,2,-2),repeat=4):
  q=list(map(cls,qs)); span={0,q[0]^q[1],q[0]^q[2],q[1]^q[2]}
  if span=={0}:continue
  p=q[0]>>1;r=q[3]>>1
  exceptional='none'
  if span=={0,1}:
   finite=(r^p,r); reciprocal=(r,r^p)
   if any(finite) and finite[0]^finite[1]==0: exceptional='one'
   if any(reciprocal) and reciprocal[1]==0:
    assert exceptional=='none';exceptional='infinity'
  counts[exceptional]+=1
 assert dict(counts)=={'none':216,'one':12,'infinity':12}
 print(counts)
if __name__=='__main__':run()
