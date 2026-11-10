from itertools import product
from pathlib import Path
checks={'quadratic_root_fibers':0,'norm_pair_counts':0,'first_pair_counts':0,'second_pair_counts':0,'exceptional_second':0,'anisotropic_rectangles':0}
for p in [2,3,5,7,11,13]:
 for a in range(1,p):
  for b in range(p):
   assert sum(a*x*x%p==b for x in range(p))<=2
   checks['quadratic_root_fibers']+=1
 for t in range(p):
  dpairs=[(x,z) for x,z in product(range(p),repeat=2) if (t*t+x*x)*(t*t+z*z)%p==0]
  assert len(dpairs)<=4*p;checks['norm_pair_counts']+=1
  for k in range(1,p):
   first=[];second=[]
   for x,z in dpairs:
    for w in range(p):
     if (k*w*w+2*t)%p==0:first.append((x,z,w))
     if (k*(t+2)*w*w-2*x*z)%p==0:second.append((x,z,w))
   assert len(first)<=8*p;checks['first_pair_counts']+=1
   if t:
    assert len(second)<=8*p;checks['second_pair_counts']+=1
    if (t+2)%p==0:
     assert len(second)<=4*p;checks['exceptional_second']+=1
   if t and k==1:
    for A,B,C in [(0,0,0),(1,2,3),(4,1,2),(p//2,p,1)]:
     for residues in [set(first),set(second)]:
      actual=sum((x%p,z%p,w%p) in residues for x,z,w in product(range(-A,A+1),range(-B,B+1),range(-C,C+1)))
      fibers=(2*A//p+1)*(2*B//p+1)*(2*C//p+1)
      assert actual<=len(residues)*fibers<=8*p*fibers
      checks['anisotropic_rectangles']+=1
# Negative control: second bound needs t !=0; k=1,t=0 atp=13 has xz=0 andw=0? P'=2w²-2xz, D=x²z² =>w0, stillsmall.
# The exception must retain freew: t=-2,p13 gives4(p-1)? exact example p5.
p=5;t=3;k=1
S=[(x,z,w) for x,z,w in product(range(p),repeat=3) if (k*(t+2)*w*w-2*x*z)%p==0 and (t*t+x*x)*(t*t+z*z)%p==0]
assert len(S)==4*p
for f in ['OriginalQuadraticResidueCount318','OriginalSecondResidueCount318','OriginalReducedResidueBounds318','OriginalAnisotropicResidueFibers318']:
 text=(Path(__file__).parent/(f+'.lean')).read_text()
 for bad in ['sorry','admit','axiom ','unsafe ']:assert bad not in text
print('PASS',checks,'exceptional negative control: free w gives20 points atp5,not4')
