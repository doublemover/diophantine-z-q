from engine import run,n
from itertools import product
from pathlib import Path
import json
def rank(xs):
 p={}
 for x in xs:
  while x:
   i=x.bit_length()-1
   if i in p:x^=p[i]
   else:p[i]=x;break
 return len(p)
def b(v,i):return (v>>i)&1
def origin(q):
 T,_,_=run(q,'finite',with_table=True)
 vals=[[[int(f.get((0,),0)) for f in v] for v in a] for a in T]
 der=[[[int(f.get((1,),0))&1 for f in v] for v in a] for a in T]
 bits=[[sum((int(h)&1)<<k for k,h in enumerate(y)) for y in x] for x in vals]
 diag=[bits[i][i] for i in range(n)]
 def frob(v): 
  w=0
  for i,d in enumerate(diag):
   if b(v,i):w^=d
  return w
 img=[1<<i for i in range(n)]
 for _ in range(4):img=[frob(x) for x in img]
 redrank=rank(img)
 rational=[]
 for v in range(1,1<<n):
  if any((v&(d^(1<<i))).bit_count()%2 for i,d in enumerate(diag)):continue
  if all((v&bits[i][j]).bit_count()%2==b(v,i)*b(v,j) for i in range(n) for j in range(i,n)):
   rows=[]
   for i in range(n):
    for j in range(i,n):
     h=vals[i][j]
     c0=b(v,i)*b(v,j)-sum(h[k] for k in range(n) if b(v,k))
     assert not c0%2
     dt=sum(der[i][j][k] for k in range(n) if b(v,k))%2
     row=bits[i][j]^(b(v,i)<<j)^(b(v,j)<<i)
     rows.append((row<<2)|(dt<<1)|((c0//2)&1))
   rational.append({'character':v,'embedding_dimension':18-rank(rows)})
 return {'q':q,'reduced_fibre_dim_over_f2':redrank,'rational':rational,'all_residue_fields_F2':len(rational)==redrank}
if __name__=='__main__':
 out=[]
 for q in product((1,-1),repeat=4):
  if q[0]==q[1]==q[2]:continue
  z=origin(q);out.append(z); print(z,flush=True)
 Path(__file__).with_name('origin-report.json').write_text(json.dumps(out,indent=2)+'\n')
