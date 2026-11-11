"""Exact finite regressions for the uniform-parameter algebra, not a Lean check.
The auxiliary polynomial weight below tests derivative bookkeeping only;
it is NOT substituted for the theorem's actual smooth compact weight.
"""
import itertools,json
import sympy as s
x,b=s.symbols('x b',real=True)
coefficients=[1,-1,-318,-326]
P={}; symbolic=0
for c in coefficients:
    phase=s.exp(s.I*b*c*x*x)
    weight=(1-x*x)**2
    v=weight
    for j in range(4):
        assert s.simplify(s.diff(weight*phase,x,j)/phase-v)==0
        P[c,j]=s.Poly(s.expand(v),b,x)
        symbolic+=1
        v=s.diff(v,x)+2*s.I*b*c*x*v
# Exact coefficient-L1 bound on [-1,1] and all sampled beta; all five
# original signs retained for both original quadrics. Actual 2pi is a
# fixed rescaling of this algebraic phase parameter, not silently a unit.
bounds=0
for kappa in [318,326]:
    cs=[1,1,-1,-1,-kappa]
    for js in itertools.product(range(4),repeat=5):
        if sum(js)>3: continue
        degree=sum(P[c,j].degree(b) for c,j in zip(cs,js))
        A=s.prod(sum(s.Abs(z) for z in P[c,j].coeffs()) for c,j in zip(cs,js))
        for t in [-7,-2,0,3,11]:
            vals=[s.Rational(-1,2),0,s.Rational(1,3),1,s.Rational(3,4)]
            value=s.prod(P[c,j].as_expr().subs({b:t,x:v}) for c,j,v in zip(cs,js,vals))
            assert s.expand_complex(value*s.conjugate(value)) <= A*A*(1+abs(t))**(2*degree)
            bounds+=1
norm_checks=0
for beta,R,xx in itertools.product(range(-9,10),range(8),range(-7,8)):
    if abs(xx)<=R:
        assert 1+max(abs(beta),abs(xx)) <= (1+abs(beta))*(1+R)
        norm_checks+=1
print(json.dumps({'status':'PASS','symbolic_phase_derivative_identities':symbolic,'five_coordinate_polynomial_beta_bounds':bounds,'exact_original_product_norm_bounds':norm_checks,'scope':'Finite algebra regressions only; arbitrary compact smooth weights and all orders are justified by the Lean source/API chain, not these samples.'},indent=2))
