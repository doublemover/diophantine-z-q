"""Exact quotient arithmetic only; no CM-classification or Igusa-membership claim."""
import json
from pathlib import Path
import sympy as s
x = s.symbols('x')
rows = []
for name, coeff, expected in [
    ('minus24', [1+s.sqrt(2), -3*(7-3*s.sqrt(2)), -3*(7+3*s.sqrt(2)), 1-s.sqrt(2)],
     [1728*(1399-988*s.sqrt(2)), 1728*(1399+988*s.sqrt(2))]),
    ('minus19', [2, -3*(1+9*s.sqrt(-19)), -3*(1-9*s.sqrt(-19)), 2], [-96**3, -96**3])
]:
    A,B,C,D = coeff
    f = sum(c*x**(3-i) for i,c in enumerate(coeff))
    def j(a,b,c,d):
        disc = s.discriminant(a*x**3+b*x*x+c*x+d,x)
        return s.simplify(256*(b*b-3*a*c)**3/(a*a*disc))
    actual = [j(A,B,C,D), j(D,C,B,A)]
    checks = [s.simplify(a-b)==0 for a,b in zip(actual,expected)]
    df = s.simplify(s.discriminant(f,x))
    dc = s.simplify(s.discriminant(f.subs(x,x*x),x))
    assert all(checks) and df != 0 and dc != 0 and A != 0 and D != 0
    rows.append({'curve':name, 'quotient_j':[str(s.expand(q)) for q in actual],
                 'expected_j_equal':checks, 'cubic_discriminant':str(df),
                 'sextic_discriminant':str(dc), 'leading_and_constant_nonzero':True})
output = {'status':'PASS', 'sympy_version':s.__version__, 'scope':'Exact polynomial quotient and smoothness checks only.', 'curves':rows}
Path(__file__).with_name('algebra-check.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
