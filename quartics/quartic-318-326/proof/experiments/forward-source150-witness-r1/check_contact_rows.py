from pathlib import Path
import re
import sympy as S
raw=Path('quartics/quartic-318-326/proof/318/Raw318FinalReplayData.lean').read_text();w=S.symbols('w0:400');t,q=S.symbols('t q');d=t-1
F=t*(t+S.Rational(1,2))*(t+1)*(t-S.Rational(1,2399))*(t+S.Rational(32,407))
vals={38:t,146:1/t,147:t**2,148:t**3,149:t**4+S.Rational(1952786,3081901)*t**5+S.Rational(1205412,3081901)*t**3,150:t**3-2*t**2,151:q,152:-q*(d**3+1),153:-t*q*d**3,154:q**2*d**6,155:q**4*d**11,156:q**7*d**18,157:q**13*d**36,158:q**25*d**72}
for i in range(107,120):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1);expr=S.sympify(re.sub(r'w (\d+)',r'w\1',e),locals={f'w{j}':x for j,x in enumerate(w)},rational=True).subs({w[j]:x for j,x in vals.items()},simultaneous=True)
 if i==112:expr-=F*q-d**2
 assert S.cancel(expr)==0,(i,S.expand(expr))
for i in range(107):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1);support=set(map(int,re.findall(r'\bw (\d+)',e)));assert not support.intersection(vals)
for i in range(120,150):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1);out=int(re.search(r'\+ \(1 \* w (\d+)\)$',e).group(1));assert out==i+39
 before=e[:e.rfind(' + (1 * w ')];assert all(int(x)<out for x in re.findall(r'\bw (\d+)',before))
print('PASS:13 contact-weight rows, exact five-factor normalization, first107 preservation, and30 triangular detector-chain gates.')
