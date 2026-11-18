import sys,itertools,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'basis'))
from engine import run,n
import numpy as np
def basis(rows,N):
 M=1<<N
 rows=np.asarray(rows,dtype=np.int64).reshape((-1,n*N)).copy()&(M-1)
 piv=[];log=0
 for c in range(n*N):
  if len(rows)==0:break
  col=rows[:,c];nz=np.flatnonzero(col)
  if not len(nz):continue
  i=nz[np.argmin(col[nz]&(-col[nz]))]
  a=int(col[i]);p=a&(-a);v=p.bit_length()-1
  w=(rows[i]*pow(a//p,-1,M))&(M-1)
  assert w[c]==p
  mult=col//p
  rows=(rows-mult[:,None]*w)&(M-1)
  extra=w*(M//p)&(M-1)
  if np.any(extra):rows=np.vstack((rows,extra))
  rows=rows[rows.any(axis=1)]
  piv.append(w);log+=N-v
 return np.asarray(piv,dtype=np.int64).reshape((-1,n*N)),log
def setup(q,N,origin):
 tab,B,_=run(q,'finite',True);m=n*N;mask=(1<<N)-1
 I=np.eye(m,dtype=np.int64);roots=[2*I,2*np.eye(m,k=n,dtype=np.int64)]
 for l in range(n):
  C=np.zeros((m,m),dtype=np.int64)
  for i in range(n):
   for k,poly in enumerate(tab[l][i]):
    for (a,),b in poly.items():
     if a<N:
      for j in range(N-a):C[j*n+i,(j+a)*n+k]+=(int(b)&mask)<<a
  C-=((origin>>l)&1)*I;roots.append(C&mask)
 R=np.diag([1<<j for j in range(N) for _ in range(n)]);groups=[(R,16*N*(N+1)//2)]
 for k in range(N):
  S,_=groups[-1]
  groups.append(basis(np.vstack([S@f for f in roots]),N))
 return roots,groups
def find(q,N=5):
 # from exact unique rational residue character in mixedpoints. In engine final basis 1 first here.
 from pathlib import Path
 sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'mixedpoints'))
 from points import fibre
 T,_,_=run(q,'finite',True);f=fibre(T,0);assert len(f)==1 and f[0]['residue_degree']==1
 tiny=[[[int(k.get((0,),0)) for k in r] for r in s] for s in T]
 origin=None
 for a in range(1,65536):
  def bit(i):return (a>>i)&1
  if all((bit(i)*bit(j)-sum(k*bit(l) for l,k in enumerate(tiny[i][j])))%2==0 for i in range(n) for j in range(i,n)):
   origin=a;break
 M=(1<<N)-1;roots,groups=setup(q,N,origin);h=[groups[k][1]-groups[k+1][1] for k in range(N)]
 print(q,'origin',origin,'Hilbert',h,flush=True)
 G2,log2=groups[2];G,log1=groups[1];S=groups[0][0]
 # retain cotangent-independent generator labels (via their generated ideals modulo m^2)
 X=G2;cur=log2;inds=[]
 for i,F in enumerate(roots):
  R,v=basis(np.vstack((X,S@F)),N)
  if v>cur:
   assert v==cur+1;cur=v;inds.append(i);X=R
 assert cur==log1
 print('cotangent generators',inds,flush=True)
 combos=sorted(range(1,1<<len(inds)),key=lambda i:(i.bit_count(),i))
 gens={v:(sum(roots[i] for j,i in enumerate(inds) if (v>>j)&1)&M) for v in combos}
 for k in range(1,N-1):
  # Find pair for gr_{k+1}. Take fibre span via separately accumulating rows in quotient.
  old,base=groups[k+2]; src=groups[k][0]; target=groups[k+1][1]
  cands={v:basis(np.vstack((old,src@G)),N) for v,G in gens.items()}
  for a,b in itertools.combinations(combos,2):
   if (cands[a][1]-base)+(cands[b][1]-base)<target-base:continue
   mat,g=basis(np.vstack((cands[a][0],cands[b][0])),N)
   if g==target:
    print('REDUCTION',k,[a,b],inds,flush=True)
    return {'q':q,'origin':origin,'truncation':N,'hilbert_function':h,'cotangent_indices':inds,'degree':k,'pair_masks':[a,b],'logs':[s for _,s in groups]}
 print('no pair',flush=True)
if __name__=='__main__':
 out=find((1,-1,1,1))
 if out:Path(__file__).with_name('first.json').write_text(json.dumps(out,indent=2)+'\n')
