"""Independent exact polynomial/support checks; not Lean kernel acceptance."""
from pathlib import Path
import re
import sympy as s
p=Path(__file__).parent
raw=(p.parents[1]/'318/Raw318FinalReplayMonolithic.lean').read_text()
rows={i:re.search(r'def r'+str(i)+r' .*? := (.*)',raw).group(1) for i in range(288)}
def expr(i,vals):
 return s.sympify(re.sub(r'w (\d+)',lambda m:'W'+m[1],rows[i]),locals={f'W{k}':v for k,v in vals.items()})
c,t,a=s.symbols('c t a',nonzero=True);r=c*c*t;d=r-1
F=r*(r+s.Rational(1,2))*(r+1)*(r-s.Rational(1,2399))*(r+s.Rational(32,407));q=c**10*d**2/F
vals={194:r,195:r*r,196:r**3,197:r**3+s.Rational(3081901,1205412)*r**4+s.Rational(976393,602706)*r**5,198:-c*c*d,199:c**4*d**2,200:c**8*d**4,201:q*d**3,202:r*r-r**3/2,203:q,204:r*q*d**3,205:q*q*d**6,206:q**4*d**11,207:q**7*d**18,208:q**13*d**36,209:q**25*d**72}
for off,start in [(0,157),(1,210)]:
 w={k+51*off:v for k,v in vals.items()};w[146]=1/t;w[143]=a;w[145]=c-a if off==0 else c
 for i in range(start,start+16):assert s.factor(expr(i,w))==0,i
for off,start in [(0,173),(1,226)]:
 translation={151:203+51*off,156:207+51*off,158:209+51*off}
 translation.update({i:i+51*(off+1) for i in range(159,191)})
 for i in range(120,151):
  mapped=re.sub(r'w (\d+)',lambda m:'w '+str(translation.get(int(m[1]),int(m[1]))),rows[i])
  assert mapped==rows[i+53*(off+1)],(off,i)
A,I=s.symbols('A I',nonzero=True);Q=(A*A-2*I*I)/(2*A);b=Q**2*F/(c**10*d**6)
assert s.cancel(b-F*(Q/(c**5*d**3))**2)==0
assert s.cancel(-q*d**3*b+r*q*d**3*b-Q**2)==0
nonpole=list(range(152))+list(range(157,205))+list(range(210,258));poles=list(range(152,157))+list(range(205,210))+list(range(258,263))
assert sorted(nonpole+poles)==list(range(263))
writes=set(range(39,51))|set(range(191,194))|set(range(242,245))|set(range(293,296))
for i in nonpole:assert not set(map(int,re.findall(r'w (\d+)',rows[i])))&writes,i
for start,base,aux,bidx in [(152,39,191,190),(205,43,242,241),(258,47,293,292)]:
 e,z,P,Q,B=s.symbols('e z P Q B');H=e*(17-B);prod=(z*z-H)*(z*z+3*H)
 v={base:e,base+1:z,base+2:P,base+3:Q,aux:e*B,aux+1:z*z,aux+2:-prod/3,bidx:B}
 for k in range(5):
  target=17*P**2-B*(17-e)*(17+3*e) if k==2 else 17*Q**2-B*prod if k==4 else 0
  assert s.expand(expr(start+k,v)-target)==0,(start,k)
print('PASS32 weight rows,60 chain relabelings,2 trace relabelings,scaled pole/squareclass,15 pole rows,248-row preservation and exact263 coverage')
