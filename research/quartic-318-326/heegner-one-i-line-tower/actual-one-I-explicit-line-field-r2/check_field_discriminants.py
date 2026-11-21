#!/usr/bin/env python3
"""Check exact polynomial scaling, ramification arithmetic and generating-bound size."""
import json,math
from pathlib import Path
import sympy as s
H=Path(__file__).resolve().parent
j=json.loads((H/'ACTUAL-DEGREE14-LINE-FIELD.json').read_text());d=j['d'];u=s.symbols('u')
c=j['actual_line_polynomial_desc']
A=26
assert all(x%A**i==0 for i,x in enumerate(c))
C=[x//A**i for i,x in enumerate(c)]
f=s.Poly.from_list(C,u,domain=s.ZZ)
disc=int(f.discriminant())
assert disc*A**(14*13)==j['polynomial_discriminant']
q=s.Poly((3*(3+2*u)**4+8*(3+2*u)**3-18*(3+2*u)**2-9).expand()/16,u)
assert q.all_coeffs()==[3,22,54,54,18]
assert all(int(x)%2==0 for x in q.all_coeffs()[1:])
assert int(q.TC())%4==2
assert int(q.discriminant()) % 32==16
# Projective inertia groups A4,V4. Every nonidentity element on
# P^1(F13) is split with exactly two fixed lines.
a4orbits=(14+11*2)//12;v4orbits=(14+3*2)//4
assert (a4orbits,v4orbits)==(3,5)
Vline=(14-a4orbits)+(14-v4orbits)//3
Vx=(84-84//12)+(84-84//4)//3
Vpoint=(168-168//24)+(168-168//8)//3+8*(168-168//2)//12
Dline=2**Vline * 3**12 * 13**13
Dx=2**Vx * 3**72 * 13**83
DF=2**Vpoint * 3**144 * 13**167 * d**84
assert (Vline,Vx,Vpoint)==(14,98,266)
assert DF//Dx**2==2**70*13*d**84 and DF%Dx**2==0
assert DF//Dline**12==2**98*13**11*d**84 and DF%Dline**12==0
assert disc%Dline==0 and (sqrindex:=math.isqrt(disc//Dline))**2==disc//Dline
# Enclose the ordinary Minkowski bound, do not treat it as runtime.
# The elementary inequalities 3.14159 < pi < 3.14160 give rational bounds.
b=math.factorial(168);den=168**168
r=math.isqrt(DF)
lo=400000**78*b*r//(314160**78*den)
hi=400000**78*b*(r+1)//(314159**78*den)
assert len(str(lo))==len(str(hi))
print(json.dumps(dict(integral_scaled_line_polynomial_desc=C,
   quartic_at2_coeffs_desc=list(map(int,q.all_coeffs())),
   line_field_discriminant=Dline,scaled_line_polynomial_index=sqrindex,
   x_field_discriminant=Dx,point_field_discriminant_decimal_digits=len(str(DF)),
   point_field_discriminant_bits=DF.bit_length(),
   point_quadratic_relative_disc_norm_factors={'2':70,'13':1,'d':84},
   point_over_line_relative_disc_norm_factors={'2':98,'13':11,'d':84},
   minkowski_standard_bound_decimal_digits=len(str(lo))),
    sort_keys=True,indent=2))
