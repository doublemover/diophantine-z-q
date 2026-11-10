"""Exact auxiliary identities only; not a polygon-cover or genus proof."""
import sympy as s
u,v,w=s.symbols('u v w',real=True)
x=u/(1-v);y=w/(1-v)
N=s.factor((x*x+y*y+1).subs(w*w,1-u*u-v*v))
assert s.factor(N-2/(1-v))==0
assert s.factor(2*x/N-u)==0
assert s.factor((N-2)/N-v)==0
x,y=s.symbols('x y',real=True);D=x*x+y*y+1
assert s.factor((1-(2*x/D)**2-((x*x+y*y-1)/D)**2)*D**2-4*y*y)==0
print('PASS: exact original Klein disk identity and inverse-coordinate formulas. No Lean, side-cover or genus claim.')
