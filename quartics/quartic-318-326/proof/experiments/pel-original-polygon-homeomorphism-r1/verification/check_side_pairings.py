#!/usr/bin/env python3
"""Independent exact arithmetic check of literal Lean coefficients and tables.
Not a Lean build or a fundamental-polygon/topological genus theorem.
"""
from pathlib import Path
import ast,re
import sympy as S
from fractions import Fraction as Q
P=Path(__file__).resolve().parent.parent
sources={f.stem:f.read_text() for f in P.glob('*.lean')}
def parse(s,env=None):
 s=s.replace('![','[').replace('^','**');env=env or {}
 def go(n):
  if isinstance(n,ast.Constant):return Q(n.value)
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,(ast.List,ast.Tuple)):return [go(x) for x in n.elts]
  if isinstance(n,ast.UnaryOp):return -go(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=go(n.left),go(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Div):return a/b
   if isinstance(n.op,ast.Pow):return a**int(b)
  raise ValueError(ast.dump(n))
 return go(ast.parse(s.strip(),mode='eval').body)
def definition(mod,name):
 text=sources[mod];a=text.index('def '+name+' ');a=text.index(':=',a)+2
 a+=len(text[a:])-len(text[a:].lstrip());depth=0
 for b in range(a,len(text)):
  if text[b]=='[':depth+=1
  if text[b]==']':
   depth-=1
   if depth==0:return text[a:b+1]
 raise ValueError(name)
def table(mod,name):return parse(definition(mod,name))
D='PELDirichletSidePairingData318';C='PELDirichletVertexCycles318';F='PELDirichletVertexFan318'
units=table(D,'coefficients');vs=table(D,'vertex');rows=table(D,'row')
partner,start,end,img0,img1=[list(map(int,table(D,n))) for n in ['partner','start','finish','imageStart','imageFinish']]
nxt,step,cl=[list(map(int,table(C,n))) for n in ['nextVertex','stepEdge','vertexClass']]
words=[list(map(int,w)) for w in table(C,'cycleWord')];sign=list(map(int,table(C,'cycleSign')))
prefix=table(F,'prefixCoordinates');pwords=[list(map(int,w)) for w in table(F,'prefixWord')];other=list(map(int,table(F,'otherVertex')));rays=table(F,'ray');scales=table(F,'rayScale');orient=list(map(int,table(F,'orientation')))
def mul(x,y):
 a,b,c,d=x;A,B,C,D=y
 return[a*A-210*b*B-84*b*D+c*C-126*d*B-42*d*D,a*B+b*A-2*b*C+3*c*B+c*D-d*C,a*C+c*A-42*b*D+c*C+42*d*B,a*D+d*A+5*b*C-5*c*B-2*c*D+3*d*C]
def emb(x):a,b,c,d=x;return[a+c/2,b+d/2,c/2,d/10]
def bar(x):a,b,c,d=x;return[a+c,-b,-c,-d]
def norm(x):r,i,j,k=emb(x);return r*r+210*i*i-5*j*j-1050*k*k
def word(w):
 z=[1,0,0,0]
 for e in w:z=mul(units[e],z)
 return z
raw=definition('PELQuaternionKleinAction318','matrix').replace('!![','[').replace(';','],[')
raw='['+raw+']'
for a,b in [('q.re','r'),('q.imI','i'),('q.imJ','j'),('q.imK','k')]:raw=raw.replace(a,b)
r,i,j,k=S.symbols('r i j k');M=S.Matrix(parse(raw,dict(zip(['r','i','j','k'],[r,i,j,k]))))
a=S.sqrt(210);b=S.sqrt(5);A=S.Matrix([[r+b*j,-a*i+a*b*k],[a*i+a*b*k,r-b*j]])
x,y,z,w=A[0,0],A[0,1],A[1,0],A[1,1]
L=S.Matrix([[x*w+y*z,a*(x*z-y*w),a*b*(x*z+y*w)],[(x*y-z*w)/a,(x*x-y*y-z*z+w*w)/2,b*(x*x+y*y-z*z-w*w)/2],[(x*y+z*w)/(a*b),(x*x+z*z-y*y-w*w)/(2*b),(x*x+y*y+z*z+w*w)/2]])
assert all(S.simplify(v)==0 for v in M-L)
J=S.diag(-S.Rational(1,1050),-S.Rational(1,5),1)
assert all(S.expand(v)==0 for v in M.T*J*M-(r*r+210*i*i-5*j*j-1050*k*k)**2*J)
def mat(u):return M.subs(dict(zip([r,i,j,k],emb(u))))
def homogeneous(u,v):return mat(u)*S.Matrix([*v,1])
def act(u,v):w=homogeneous(u,v);assert w[2]>0;return[w[0]/w[2],w[1]/w[2]]
for e,u in enumerate(units):
 assert norm(u)==1 and mul(units[partner[e]],u)==[-1,0,0,0]
 assert partner[partner[e]]==e and partner[e]!=e
 mm=mat(u);assert list(mm.row(2)*2-S.Matrix([[0,0,2]]))==[rows[e][1],rows[e][2],rows[e][0]]
 assert act(u,vs[start[e]])==vs[img0[e]] and act(u,vs[end[e]])==vs[img1[e]]
 assert homogeneous(u,vs[start[e]])[2]==homogeneous(u,vs[end[e]])[2]==1
 assert {img0[e],img1[e]}=={start[partner[e]],end[partner[e]]}
for v in range(28):
 assert vs[v][0]**2/1050+vs[v][1]**2/5<1
 e=step[v];assert (v,nxt[v]) in [(start[e],img0[e]),(end[e],img1[e])]
 assert cl[v]==cl[nxt[v]] and {v,other[v]}=={start[e],end[e]}
 assert word(pwords[v])==prefix[v]
 mm=mat(bar(prefix[v]));w=homogeneous(bar(prefix[v]),vs[v]);dv=mm*S.Matrix([vs[other[v]][0]-vs[v][0],vs[other[v]][1]-vs[v][1],0]);assert w[2]>0
 tangent=[(dv[t]*w[2]-w[t]*dv[2])/w[2]**2 for t in range(2)]
 assert scales[v]>0 and tangent==[scales[v]*rays[v][t] for t in range(2)]
for e in range(28):assert cl[start[e]]==cl[img0[e]] and cl[end[e]]==cl[img1[e]]
for a in range(28):
 reach={a};v=a
 for _ in range(7):v=nxt[v];reach.add(v)
 assert reach=={b for b in range(28) if cl[b]==cl[a]}
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def crossing(a,b):
 if a[1]<=0<b[1] and cross(a,b)>0:return 1
 if b[1]<=0<a[1] and cross(a,b)<0:return -1
 return 0
for c in range(5):
 members=[v for v in range(28) if cl[v]==c]
 assert len(members)==[8,8,4,4,4][c] and word(words[c])==[sign[c],0,0,0]
 assert all(orient[c]*cross(rays[v],rays[nxt[v]])>0 for v in members)
 assert sum(crossing(rays[v],rays[nxt[v]]) for v in members)==orient[c]
print('PASS: literal original representation, quadratic form,28 units/sides,14 inverse pairs,5 exact graph classes/cycle products,28 original tangent rays and5 signed axis turns. No topological polygon/genus claim.')
