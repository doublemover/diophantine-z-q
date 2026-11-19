import json,collections,hashlib,pathlib,sys,math
P=pathlib.Path('lowvars-pub7'); old=P/'public/computation/quartic/seven_units193_v74/compact/quadratic-family.json'; N=P/'new192'; read=lambda f:json.loads(f.read_bytes())
c=read(N/'certificate.json'); o=read(old); n=read(N/'quadratic-family.json'); poly=read(N/'polynomial-family.json')
ren={int(k):v for k,v in c['renumber'].items()}; U={int(k):tuple(v) for k,v in c['oldunits'].items()}; NU={ren[int(k)]:tuple(v) for k,v in c['units'].items()}; w=c['weights']; assert sorted(ren.values())==list(range(1,193));assert set(U)==set(range(1,194))-ren.keys();assert ren[1]==1
def view(row,old=True):
 d=collections.Counter()
 for t in row['terms']:
  a=b=0; m=[]
  for x in t['monomial']:
   if old:
    if x in U: A,B=U[x]
    else:
     A,B=[w.get('x%d_%d'%(x,i),0) for i in (0,1)];m.append(ren[x])
   else:
    A,B=NU.get(x,(0,0))
    if x not in NU:m.append(x)
   a+=A;b+=B
  d[(int(t['parameterPower']),tuple(sorted(m)),a,b)]+=int(t['coefficient'])
 return {k:v for k,v in d.items() if v}
assert view({'terms':[{'parameterPower':0,'monomial':[1],'coefficient':1}]})=={(0,(1,),0,0):1}
for ro,rn in zip(o['residuals'][:162],n['residuals'][:162],strict=True):
 a=view(ro);b=view(rn,False); L=sorted(a);R=sorted(b);i,j=L[0][2]-R[0][2],L[0][3]-R[0][3]; factor=a[L[0]]//b[R[0]]; assert factor in (-1,1)
 assert { (p,m,x+i,y+j):v*factor for (p,m,x,y),v in b.items()}==a,(ro['id'],i,j)
assert all(not view(r) for r in o['residuals'][162:]);assert all(not view(r,False) for r in n['residuals'][162:])
s=collections.Counter()
for r in n['residuals']:
 for l in r['terms']:
  for t in r['terms']:
   assert len(l['monomial'])<=2
   s[(l['parameterPower']+t['parameterPower'],tuple(sorted(l['monomial']+t['monomial'])))]+=int(l['coefficient'])*int(t['coefficient'])
s={k:v for k,v in s.items() if v}; p={(t['parameterPower'],tuple(t['monomial'])):int(t['coefficient']) for t in poly['terms']};assert s==p and len(p)==len(poly['terms']);assert {i:v for (i,m),v in s.items() if m==(1,)*4}=={0:1}
print('PASS',len(s),'terms',len(set(k[1] for k in s)),'fixed-C monomial slots, coefficient x^4=1; sha source',hashlib.sha256(old.read_bytes()).hexdigest());print(o['fixedParameter'])
