"""Exact algebra/support checks, not Lean kernel acceptance."""
from pathlib import Path
import re
import sympy as s
p=Path(__file__).parent
raw=(p.parents[1]/'318/Raw318FinalReplayMonolithic.lean').read_text()
rows={i:re.search(r'def r'+str(i)+r' .*? := (.*)',raw).group(1) for i in range(288)}
def expr(i,w):
 return s.sympify(re.sub(r'w (\d+)',lambda m:'W'+m[1],rows[i]),locals={'S':s.Symbol('S'),**{f'W{k}':v for k,v in w.items()}})
q,f,H,r,A,B,C,D,I=s.symbols('q f H r A B C D I',nonzero=True)
x=q+q*q;f4=x*x+s.Rational(496408687,100291113)*x**3+s.Rational(197130368,33430371)*x**4
rpoly=101783690143177584*x+267108917866935984*x*x+533801448346128768*f4+4376874610839020
N=1+(H/r)**2+2*f/r;Q=I/(H*r**15);W=N*N+r*Q*Q;quot=W/(1+114444*r)
v={0:q,33:f,37:H,82:A,83:B,118:q*q,296:x*x,297:f4,298:1/r,299:1/r**2,300:1/r**4,301:1/r**8,302:1/r**16,303:C,304:D,305:A*C+2*B*D,306:A*D+B*C,307:C*C-2*D*D,308:I,309:H/r,310:Q,311:N-1,312:Q*Q,313:quot,314:114444*r*quot**2}
for i in range(263,282):
 e=s.factor(expr(i,v))
 if i in (265,276,280):
  numerator=s.fraction(e)[0]
  e=s.rem(numerator,r-rpoly,r)
 if i==275:e=s.cancel(e.subs(I,1/(C*C-2*D*D)))
 if i in (272,273):
  rt=s.sqrt(2);k=-1+s.Rational(7,4)*rt;m=s.Rational(39,8)-s.Rational(9,2)*rt;disc=11-6*rt
  z=A+B*rt;w=C+D*rt;poly=s.expand((z*w)**2-k*k*w*w-2*m*z*w-k*k*z*z-disc)
  target=poly.coeff(rt,1) if i==273 else poly.subs(rt,0)
  assert s.expand(e-target)==0,i
 else:assert e==0,(i,e)
# The source scalar squareclass is 114444*r, equivalently 11*r times102².
assert 114444==11*102**2
assert s.cancel(v[314]-(11*r)*(102*quot)**2)==0
u,z,k,m,disc=s.symbols('u z k m disc',nonzero=True)
a=-1/u;b=-1/(u*z)
kum=(a*b)**2-k*k*b*b-2*m*a*b-k*k*a*a-disc
comp=1-k*k*(u*u+u*u*z*z)-2*m*u*u*z-disc*u**4*z*z
assert s.cancel(kum*u**4*z*z-comp)==0
a,b=s.symbols('a b');kum=(a*b)**2-k*k*b*b-2*m*a*b-k*k*a*a-disc
identity=(k*k*a-b*(a*b-m))**2-k*k*(b**4-disc)
assert s.expand(identity-(b*b-k*k)*kum-b*b*(m*m-k**4+disc))==0
# Final six rows, preserving all263 earlier rows and all19 scalar gates.
e,z,P,Q,b,X,Y,Z,S,a,i=s.symbols('e z P Q b X Y Z S a i')
prod=(z*z-e*(17-b))*(z*z+3*e*(17-b))
v={51:e,52:z,53:P,54:Q,55:X,56:Y,57:Z,145:a,308:i,314:b,315:e*b,316:z*z,317:-prod/3}
for j in range(282,288):
 target=17*P*P-b*(17-e)*(17+3*e) if j==285 else 17*Q*Q-b*prod if j==286 else X*X+6*Y*Y-2*Z*Z-3*(4096*a*S+i)**2+2*S*S if j==287 else 0
 assert s.expand(expr(j,v)-target)==0,j
writes=set(range(51,58))|set(range(296,318))
for j in range(263):assert not set(map(int,re.findall(r'w (\d+)',rows[j])))&writes,j
for j in range(263,282):assert not set(map(int,re.findall(r'w (\d+)',rows[j])))&(set(range(51,58))|set(range(315,318))),j
src=(p/'ScalarCompleteSource318.lean').read_text();parts=re.search(r'  exact ⟨(hw\'.*?)⟩',src).group(1).split(',')
expected=[]
for h,n in [("hw'",263),("hs'",19),('hp',6)]:
 expected += [h+'.2'*j+('.1' if j<n-1 else '') for j in range(n)]
assert parts==expected
assert len(parts)==288
print('PASS19 scalar rows, actual reciprocal/quartic identities,11*r scalar squareclass,6 final rows,263+19 preservation,exact288 projections')
