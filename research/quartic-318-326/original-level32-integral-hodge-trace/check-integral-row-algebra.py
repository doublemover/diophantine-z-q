#!/usr/bin/env python3
"""Exact symbolic check of the two birational maps and differential sign."""
import sympy as s

x, y, U, V = s.symbols("x y U V")
g = s.groebner([x**2+y**4-1], x, y)
g2 = s.groebner([V**2-U**3-4*U], V, U)
u, v = 2*(1+x)/y**2, 4*(1+x)/y**3
x_back, y_back = U*(2*U/V)**2/2-1, 2*U/V

def zero_mod(expr, gb):
    num, den = s.fraction(s.factor(expr))
    assert gb.reduce(s.expand(num))[1] == 0, (expr, num)
    assert gb.reduce(s.expand(den))[1] != 0, (expr, den)

zero_mod(v**2-u**3-4*u, g)
zero_mod(x_back**2+y_back**4-1, g2)
zero_mod(x_back.subs({U:u, V:v}, simultaneous=True)-x, g)
zero_mod(y_back.subs({U:u, V:v}, simultaneous=True)-y, g)
zero_mod(u.subs({x:x_back, y:y_back}, simultaneous=True)-U, g2)
zero_mod(v.subs({x:x_back, y:y_back}, simultaneous=True)-V, g2)
du = s.diff(u, x) + s.diff(u, y) * (-x/(2*y**3))
zero_mod(du/(2*v)-1/(4*y**3), g)
assert (-16*(4*4**3)) == -(2**12)
assert u.subs({x:0,y:1}) == 2 and v.subs({x:0,y:1}) == 4
print("PASS: both birational compositions, actual differential sign, cusp coordinates and discriminant")
