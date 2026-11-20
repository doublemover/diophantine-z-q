from pathlib import Path
from hashlib import sha256
import json,sys
F=Path(sys.argv[1]); B=Path(sys.argv[2])
assert sha256(B.read_bytes()).hexdigest()=='421d8068d858eed68da492cb75d9d3b1e9bb3d2163eb10f3f762754504db1b3f'
w=json.loads(B.read_text()); tab={tuple(r['T']+r['U']):r['rows'][0]['phi'] for r in w['records']}
p=53
# New coordinate X_old=X_short+2/3 followed by short Weierstrass weighted projective operations.
# F_53^2 pair coefficient representation. The identity chart has Z=0.
zero=(0,0); one=(1,0); da=(2*pow(3,-1,p)%p,0); ca=(-13*pow(3,-1,p)%p,0); cb=(-70*pow(27,-1,p)%p,0)
def fadd(x,y):return ((x[0]+y[0])%p,(x[1]+y[1])%p)
def sc(k,x):return (k*x[0]%p,k*x[1]%p)
def sub(x,y):return fadd(x,sc(-1,y))
def mul(x,y):return ((x[0]*y[0]+22*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def s(x):return mul(x,x)
def cube(x):return mul(s(x),x)
def recip(x):
 k=pow((x[0]*x[0]-22*x[1]*x[1])%p,-1,p);return (k*x[0]%p,-k*x[1]%p)
O=(one,one,zero)
def double(A):
 X,Y,Z=A
 if Z==zero or Y==zero:return O
 YY=s(Y); S=sc(4,mul(X,YY)); M=fadd(sc(3,s(X)),mul(ca,s(s(Z))))
 t=sub(s(M),sc(2,S))
 return (t,sub(mul(M,sub(S,t)),sc(8,s(YY))),sc(2,mul(Y,Z)))
def add(A,B):
 X,Y,Z=A; x,y,z=B
 if Z==zero:return B
 if z==zero:return A
 U=mul(X,s(z)); u=mul(x,s(Z)); V=mul(Y,cube(z)); v=mul(y,cube(Z))
 H=sub(u,U); r=sc(2,sub(v,V))
 if H==zero:return O if r!=zero else double(A)
 I=s(sc(2,H)); J=mul(H,I); W=mul(U,I)
 t=sub(sub(s(r),J),sc(2,W))
 return (t,sub(mul(r,sub(W,t)),sc(2,mul(V,J))),sc(2,mul(H,mul(Z,z))))
def times(n,A):
 B=O
 for v in bin(n)[2:]:
  B=double(B)
  if v=='1': B=add(B,A)
 return B
def aff(A):
 X,Y,Z=A
 if Z==zero:return None
 a=recip(Z);return (fadd(mul(X,s(a)),da),mul(Y,cube(a)))
def to_jac(A):
 if A is None:return O
 x,y=map(tuple,A); x=sub(x,da)
 assert s(y)==fadd(fadd(cube(x),mul(ca,x)),cb)
 return (x,y,one)
G=to_jac([[22,0],[0,15]])
assert aff(times(13,G)) is None and aff(G) is not None
expect={323:(24,9,11,(42,11)),132107:(720,1,7,(24,31)),
        1139:(96,11,12,(11,46)),465851:(1248,7,10,(44,51))}
for d,e in expect.items():
 o=json.loads((F/f'{d}.json').read_text())
 points=[to_jac(tab[tuple(r['chart'])]) for r in o['all_exact_marks_of_chosen_trace']]
 assert len(points)==o['ring_class_number']
 T=O
 for row,A in zip(o['all_exact_marks_of_chosen_trace'],points):
  assert aff(times(224,A))==aff(times(row['projection_mod_13'],G))
  T=add(T,A)
 assert aff(T)==tuple(map(tuple,o['finite_group_raw_ring_sum']))
 S=times(224,T)
 assert aff(S)==aff(times(o['chosen_ring_trace_mod13'],G))
 H=times(7,S)
 assert aff(H)==aff(times(o['chosen_maximal_Hilbert_trace_mod13'],G))
 x,y=aff(H)
 rho=tuple(o['finite_group_twist_root'])
 assert s(rho)==(-d%p,0)
 X=sc(-d,x);Y=mul(cube(rho),y)
 assert X[1]==Y[1]==0 and (X[0],Y[0])==tuple(o['finite_group_hilbert_projection_twisted'])
 assert (len(points),o['chosen_ring_trace_mod13'],o['chosen_maximal_Hilbert_trace_mod13'],(X[0],Y[0]))==e
 print(d,len(points),aff(T),o['chosen_ring_trace_mod13'],o['chosen_maximal_Hilbert_trace_mod13'],(X[0],Y[0]))
