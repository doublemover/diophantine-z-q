#!/usr/bin/env python3
"""Independent literal original-order/unit/table verification; not Lean acceptance."""
from pathlib import Path
from fractions import Fraction as Q
import itertools,re,ast
P=Path(__file__).resolve().parent.parent
s=(P/'PELGlobalIntegralUnitLifts318.lean').read_text()
def table(name):
 tail=s.split('def '+name,1)[1].split('\n@[expose]',1)[0].split('\n\n',1)[0]
 return [tuple(ast.literal_eval('['+x+']')) for x in re.findall(r'!\[([^\[\]]+)\]',tail)]
g=table('generatorCoefficients');inv=table('inverseCoefficients')
assert len(g)==len(inv)==3
fg=[tuple(map(int,x.split(','))) for x in re.findall(r'⟨([0-9,]+)⟩',s.split('def finiteGenerator',1)[1].split('\n\n',1)[0])]
assert len(fg)==3
# Independent structure constants i²=-210,j²=5,ij=-ji=k.
def mul(x,y,a=-210,b=5):
 r,i,j,k=x;R,I,J,K=y
 return (r*R+a*i*I+b*j*J-a*b*k*K,r*I+i*R-b*j*K+b*k*J,r*J+j*R+a*i*K-a*k*I,r*K+k*R+i*J-j*I)
def embed(x):return (Q(x[0])+Q(x[2],2),Q(x[1])+Q(x[3],2),Q(x[2],2),Q(x[3],10))
def norm(x):r,i,j,k=x;return r*r+210*i*i-5*j*j-1050*k*k
def reduction(x):a,b,c,d=x;return ((a-c)%3,(b-d)%3,(-c)%3,d%3)
for i in range(3):
 assert mul(embed(g[i]),embed(inv[i]))==(1,0,0,0)
 assert mul(embed(inv[i]),embed(g[i]))==(1,0,0,0)
 assert norm(embed(g[i]))==(-1 if i==0 else 1)
 assert reduction(g[i])==fg[i]
def fm(x,y):return tuple(v%3 for v in mul(x,y,0,2))
def pw(x,n):
 z=(1,0,0,0)
 for _ in range(n):z=fm(z,x)
 return z
def word(k,a,b):return fm(fm(pw(fg[0],k),pw(fg[1],a)),pw(fg[2],b))
def fn(x):return (x[0]*x[0]-2*x[2]*x[2])%3
# Parse and validate EACH emitted witness, respecting the literal fin_cases order.
proof=s.split('theorem finite_cover',1)[1].split('  fin_cases r <;> fin_cases u <;> fin_cases j <;> fin_cases v\n',1)[1]
blocks=proof.split('  · ')[1:]
assert len(blocks)==81
images=[]
for x,block in zip(itertools.product(range(3),repeat=4),blocks):
 if x[0]==x[2]==0:
  assert block.startswith('exfalso') and 'apply hx' in block
 else:
  m=re.match(r'exact ⟨(\d+),(\d+),(\d+),by ext',block);assert m,(x,block)
  k,a,b=map(int,m.groups());assert k<8 and a<3 and b<3
  assert word(k,a,b)==x,(x,k,a,b)
  assert fn(x)==pow(-1,k,3)
  images.append(x)
assert len(set(images))==72
assert sum(fn(x)==1 for x in images)==36
assert len({min(x,tuple((-a)%3 for a in x)) for x in images})==36
assert len({min(x,tuple((-a)%3 for a in x)) for x in images if fn(x)==1})==18
print('PASS: literal3 global inverse/norm/reduction pairs; all81 emitted branches and72 exact lifts; norm-one36 vs full72 and projective18 vs36. No Lean or moduli acceptance.')
