#!/usr/bin/env python3
"""Exact symbolic preflight only; not a Lean/kernel proof check."""
import sympy as s
A,B,C,D,a,b,z,w=s.symbols('A B C D a b z w')
f=lambda t:(t-a)/(t-b)
g=lambda t:(b*t-a)/(t-1)
assert s.cancel(g(f(z))-z)==0
assert s.cancel(f(g(w))-w)==0
assert s.cancel(s.diff(f(z),z).subs(z,a)-1/(a-b))==0
ha=A*a+B-a*(C*a+D)
hb=A*b+B-b*(C*b+D)
ht=A+D
hs=C*(a+b)+2*D
hp=B+C*a*b
assert s.expand((a-b)*hs-(-ha+hb+(a-b)*ht))==0
assert s.expand(hp-(ha-a*ht+a*hs))==0
cross=(A*z+B-a*(C*z+D))*(z-b)+(A*z+B-b*(C*z+D))*(z-a)
assert s.expand(cross-((-a*z-b*z+2*z*z)*ht+(a*b-z*z)*hs+(-a-b+2*z)*hp))==0
assert s.expand((z-w)*(z+w)-(z*z-w*w))==0
print('PASS: exact coordinate inverse, derivative, sign-conjugation certificates and square fibers; not a Lean proof check.')
