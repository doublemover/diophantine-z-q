#!/usr/bin/env python3
"""Exact I=673 framed T13, preserving the T17 basis through its Fp^4 subfield."""
from pathlib import Path
from hashlib import sha256
import json,time,sys,random
d=Path(__file__).resolve().parent.parent/'ct-level48-cm192-helper673-framed-t17-r1'
raw=(d/'replay_helper673_framed_t17.py').read_bytes()
assert sha256(raw).hexdigest()=='2fd85fd268649770688a677451c18769ae3478915e0c879732f46154bf97ffe0'
blob=(d/'EXACT-HELPER673-FRAMED-T17.json').read_bytes()
assert sha256(blob).hexdigest()=='2745f5eceb36ad4d40b40e113433cf4da673893f107c538260f616c7d03fa4b1'
base=json.loads(blob)
s=raw.decode(); s=s[:s.index('# Supersingular j via')].replace('n=32','n=12').replace('M17=p**16-1','M13=p**6-1')
left=s.index('c=pow');right=s.index('def norm',left)
s=s[:left]+'''c2=base["field_relation_c"]; c3=pow(next(i for i in range(2,p) if pow(i,(p-1)//3,p)!=1),(p-1)//3,p)
assert pow(c3,3,p)==1 and c3!=1
c=(c2**3*c3)%p
assert pow(c,96,p)==1 and pow(c,48,p)!=1 and pow(c,32,p)!=1
assert pow(p,12,1152)==1 and pow(p,6,1152)!=1 and pow(p,4,1152)!=1
'''+s[right:]
s=s.replace('assert ex(step_t,32)==c','assert ex(step_t,12)==c')
# The generic square root chooses a nonsquare from the 2-part of the subfield.
s=s.replace(' z=1<<(w*(n//deg)) if deg>1 else c',' z=1<<(w*(n//deg)) if deg>1 else c')
exec(s)
Y=ex(step_t,513)
assert ex(Y,4)==base["field_relation_c"] and ex(Y,128)==1 and ex(Y,64)!=1
def decode(a):
 z=0
 for i,k in a:
  assert i%8==0
  z=add(z,scl(k,ex(Y,i//8)))
 return z
RNG=random.Random(67313);start=time.time()
def random_pt(A,B):
 while True:
  x=sum(RNG.randrange(p)<<(w*i) for i in range(n))
  y=sqroot(add(fmul(x,add(sq(x),A)),B),12)
  if y is not None:return x,y,1
def basis13(A,B):
 U=[]
 for _ in range(120):
  T=JP(M13//13,random_pt(A,B),A)
  if T is None:continue
  assert JP(13,T,A) is None
  if not U:
   U.append(T);axis=toA([JP(i,T,A) for i in range(13)],12);continue
  if toA([T],12)[0] not in axis:return U[0],T
 raise ValueError("entropy")
models=[]
for j0,pp in zip(base['j'],base['order32_and_3_bases']):
 j=decode(j0); A,B=ab(j)
 qq=[tuple(decode(x) for x in z0) for z0 in pp]
 assert all(curve(u,A,B) for u in qq)
 d32={v:i for i,v in enumerate(Jgrid(32,fromA(qq[0]),fromA(qq[1]),A,4))}
 d3={v:i for i,v in enumerate(Jgrid(3,fromA(qq[2]),fromA(qq[3]),A,4))}
 u,v=basis13(A,B); z=Jgrid(13,u,v,A,12)
 models.append(dict(j=j,A=A,B=B,q=qq,d32=d32,d3=d3,points13=z))
 if "--progress" in sys.argv and len(models)%8==0: print('models',len(models),time.time()-start,file=sys.stderr)
idx={m['j']:j for j,m in enumerate(models)}
# Same exact propers and scaling convention as the fixed T17 donor.
raw_s=raw.decode(); gg=raw_s[raw_s.index('def VELU('):raw_s.index('edges=[]; FROB=[]')]
gg=gg.replace('for z,_ in K],32)', 'for z,_ in K],12)')
exec(gg)
edges=[]
for j,m in enumerate(models):
 rows=[]
 for ell in range(14):
  pc=[m['points13'][(z*13+(z*ell)%13) if ell<13 else z] for z in range(1,13)]
  assert len(set(pc))==12 and all(pc)
  ta,tb,rr=VELU(m['q'],m['A'],m['B'],pc)
  q=cal_j(ta,tb);d=idx[q];dd=models[d]
  a,b=div(ta,dd['A'],2),div(tb,dd['B'],2)
  u2=div(b,a,2);u=sqroot(u2,4)
  assert u and sq(u2)==a and fmul(sq(u2),u2)==b
  rr=[(div(x,u2,4),div(y,fmul(u,u2),4)) for x,y in rr]
  assert all(curve(P,dd['A'],dd['B']) for P in rr)
  mm=mat(rr,dd)
  dt=lambda a,b:(a[0]*b[1]-a[1]*b[0])
  assert dt(*mm[:2])%2==1 and dt(*mm[2:])%3!=0
  rows.append([d,mm])
 edges.append(rows)
 if "--progress" in sys.argv and (j+1)%8==0: print('edges',j+1,time.time()-start,file=sys.stderr)
q=raw_s[raw_s.index('def pmul('):raw_s.index('for j,(a,mat0)')]
exec(q)
q=raw_s[raw_s.index('def mprod('):raw_s.index('out=dict(')].replace('diag17','diag13').replace('[[17,0],[0,17],[2,0],[0,2]]','[[13,0],[0,13],[1,0],[0,1]]')
FROB=base['FrobI'];exec(q)
print(json.dumps(dict(p=p,cubic=c3,one_generator_relation=c,Y_as_W_power=513,T13=edges,
                      checked_dual_edges=784,checked_frobenius_commutation_rows=56,
                      scope="exact additional helper-compatible operator in same frame, no moving key or mark"),
                 sort_keys=True,separators=(',',':')))
