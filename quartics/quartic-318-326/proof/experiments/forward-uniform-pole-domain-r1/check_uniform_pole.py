"""Independent exact identities/support checks; not a Lean or arithmetic proof."""
from pathlib import Path
import re
import sympy as s
p=Path(__file__).parent
q=(p/'ContactChainWitness318.lean').read_text();r=(p/'ContactChainReal318.lean').read_text()
for i in range(159,189):
 a=re.search(r'def value'+str(i)+r' .*? := (.*)',q).group(1)
 c=re.search(r'def value'+str(i)+r' .*? := (.*)',r).group(1)
 assert a==c,(i,a,c)
 assert all(j<146 or j in (151,156,158) for j in map(int,re.findall(r'w (\d+)',a)))
b,e,z,y1,y2=s.symbols('b e z y1 y2',nonzero=True)
B=17*b;V=B**2*(1-b/17)
f1=y1**2-B*(B-e)*(B+3*e)
f2=y2**2-B*z**2*(B*z**2-e*V)*(B*z**2+3*e*V)
E=e/b;Z=z/b;P=y1/B;Q=17*y2/(B**3*z)
assert s.cancel(17*P**2-b*(17-E)*(17+3*E)-f1/(17*b**2))==0
assert s.cancel(17*Q**2-b*(Z**2-E*(17-b))*(Z**2+3*E*(17-b))-f2/(4913*b**6*z**2))==0
raw=(p.parents[1]/'318/Raw318FinalReplayMonolithic.lean').read_text()
e,z,P,Q=s.symbols('e z P Q');W=s.symbols('w0:318');vals={39:e,40:z,41:P,42:Q,190:b,191:e*b,192:z*z,193:-(z*z-e*(17-b))*(z*z+3*e*(17-b))/3}
for i in range(152):
 line=re.search(r'def r'+str(i)+r' .*',raw).group()
 assert not set(map(int,re.findall(r'w (\d+)',line)))&{39,40,41,42,191,192,193}
for i in range(152,157):
 body=re.search(r'def r'+str(i)+r' .*? := (.*)',raw).group(1)
 expr=s.sympify(re.sub(r'w (\d+)',lambda m:'w'+m[1],body),locals={str(x):x for x in W})
 expr=expr.subs({W[k]:v for k,v in vals.items()},simultaneous=True)
 expected=17*P**2-b*(17-e)*(17+3*e) if i==154 else 17*Q**2-b*(z*z-e*(17-b))*(z*z+3*e*(17-b)) if i==156 else 0
 assert s.expand(expr-expected)==0,i
print('PASS:30 exact real gates, coefficient support, two point conversions, five literal rows, prior-row preservation')
