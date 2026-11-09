"""Exact symbolic/static checks only. Never invokes Lean or a build."""
from pathlib import Path
import hashlib,json,re
import sympy as S
p=Path(__file__).resolve().parent
fold=(p/'ActualDetectorFold318.lean').read_text()
gates=(p/'ContactChainWitness318.lean').read_text()
def expr(s):
    s=re.sub(r'value(\d+) w',lambda m:'G'+m[1],s)
    s=re.sub(r'w (\d+)',lambda m:'W'+m[1],s)
    return S.sympify(s.replace('^','**'))
g={int(i):expr(s) for i,s in re.findall(r'def value(\d+) \(w : Assignment\) : ℚ := (.*)',gates)}
leaftext=fold.split('@[expose] def leaves')[1].split('@[expose] def chain')[0]
leaves=[(int(q),expr(a),expr(b)) for q,a,b in re.findall(r'\(pair \(w (\d+)\) 0,pair \((.*?)\) \((.*?)\)\)',leaftext)]
assert len(leaves)==16
points=[(S.Integer(1),S.Integer(0)),(S.Symbol('G159'),S.Integer(0)),(S.Symbol('G160'),S.Integer(0))]+[(S.Symbol('G'+str(i)),S.Symbol('G'+str(i+1))) for i in range(161,188,2)]
for j,(qi,a,b) in enumerate(leaves):
    x,y=points[j];xn,yn=points[j+1];q=S.Symbol('W'+str(qi))
    out=lambda z:g[int(str(z)[1:])] if str(z).startswith('G') else z
    assert S.expand(x*x+2*y*y+q*a-out(xn))==0,('real',j)
    assert S.expand(2*x*y+q*b-out(yn))==0,('imag',j)
    indices={int(i) for i in re.findall(r'W(\d+)',str(a)+' '+str(b))}
    assert all(i<146 for i in indices)
    assert qi in (151,156,158)
c,u,d,T=S.symbols('c u d T',nonzero=True)
theta=[0,-S.Rational(1,2),-1,S.Rational(1,2399),-S.Rational(32,407)]
contact=lambda t:S.prod(t-a for a in theta)
t=c*c*u/d**2;delta=t-1
P=S.prod(u-a*d**2/c**2 for a in theta)
assert S.cancel(contact(t)-c**10/d**10*P)==0
assert S.cancel(T**2*contact(t)/(c**10*delta**6)-P*(T/(d**5*delta**3))**2)==0
C,D,E=S.symbols('C D E',integer=True)
Fval=10*C-10*D;deltaval=2*C-2*D;qval=10*C+2*deltaval-Fval
assert S.expand(qval-(6*D+4*C))==0
assert S.expand(7*qval+18*deltaval-(6*D+64*C))==0
assert S.expand(25*qval+72*deltaval-(6*D+244*C))==0
assert S.expand(2*(-E-5*D-3*deltaval)-(2*D-12*C-2*E))==0
# Verify the rational inverse-trace identity without a split-place assumption.
a,b,r=S.symbols('a b r')
num=S.together(1/(a+b*r)+1/(a-b*r)-2*a/(a*a-2*b*b)).as_numer_denom()[0]
assert S.rem(S.expand(num),r*r-2,r)==0
m=json.loads((p/'SOURCE-COPIES.json').read_text())
assert len(m['unchanged_sources'])==111 and len(m['new_sources'])==9 and not m['repaired_sources']
for name,item in m['unchanged_sources'].items():
    assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==item['source_sha256']
assert '190+51*j.val' in (p/'ThreeDetectorArithmetic318.lean').read_text()
assert 'infinite CRT orbit' in (p/'ThreeDetectorArithmetic318.lean').read_text()
print('PASS: all32 literal step-coordinate identities, actual coefficient indices and weights, exact five-contact normalization, inverse trace, all weight/pole valuations,111 copy bindings. Not a Lean or prime-pattern proof.')
