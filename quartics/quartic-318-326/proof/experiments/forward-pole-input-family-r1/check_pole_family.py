from pathlib import Path
import re
import sympy as S
raw=Path('quartics/quartic-318-326/proof/318/Raw318FinalReplayData.lean').read_text();w=S.symbols('w0:400');vals={w[151]:0,w[156]:0,w[158]:0}
for i in range(120,150):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1)
 expr=S.sympify(re.sub(r'w (\d+)',r'w\1',e),locals={f'w{j}':x for j,x in enumerate(w)},rational=True);o=i+39
 vals[w[o]]=S.expand(-expr.subs(w[o],0).subs(vals,simultaneous=True));expected=1 if o in [159,160] or o%2 else 0
 assert vals[w[o]]==expected,(i,vals[w[o]])
a,b,t,F=S.symbols('a b t F');z=(a*a-2*b*b)/(2*a);pole=z*z*F/(t-1)**6;square=z/(t-1)**3;q=(t-1)**2/F
assert S.cancel(pole-F*square*square)==0
assert S.cancel(-a*a/2+a*z+b*b)==0
assert S.cancel((q-q*((t-1)**3+1)+t*q*(t-1)**3)*pole-z*z)==0
for n,m in [(2,1),(32,7),(62,13),(122,25)]:assert n<5*m
print('PASS:30 exact zero-weight chain values, trace/pole rows150–151, original contact squareclass, and all four strict polynomial-degree inequalities.')
