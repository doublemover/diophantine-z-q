import sympy as s,json,hashlib
from pathlib import Path
k,t,x,z,w=s.symbols('k t x z w')
P=k*w*w+2*t;PP=k*(t+2)*w*w-2*x*z
K=(k*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2
D=(t*t+x*x)*(t*t+z*z)
Ds=((t+2)**2+x*x)*((t+2)**2+z*z)
assert s.expand(K-D-P*(P+2*t*t-2*x*z))==0
quo,rem=s.div(s.expand((t+2)**2*K-t*t*Ds),PP,w)
assert s.expand(rem)==0
# Actual original quadric, nonzero original t and permitted odd prime.
a,b,c,d,W,kap,p=-5,-1,-5,-1,0,1,17
T=a+c;X=b-d;Z=b+d
assert a*a+b*b-c*c-d*d-kap*W*W==0
G=(a+1)**2+b*b;H=(c+1)**2+d*d
sub={k:kap,t:T,x:X,z:Z,w:W}
assert G%p==H%p==int(PP.subs(sub))%p==int(K.subs(sub))%p==0
assert T and p>3 and kap%p and T%p
assert int(D.subs(sub))%p==13 and int(Ds.subs(sub))%p==0
# Correct exceptional t=-2 retains K, NOT the shifted D, which collapses to x²z².
assert s.expand(K.subs(t,-2))==(k*w*w-x*z)**2+4*(x+z)**2 or s.expand(K.subs(t,-2)-((k*w*w-x*z)**2+4*(x+z)**2))==0
assert s.expand(K.subs({t:-2,x:0}))==k*k*w**4+4*z*z
assert s.expand(K.subs({t:-2,z:0}))==k*k*w**4+4*x*x
print(json.dumps({'status':'PASS','counterexample':{'kappa':kap,'coordinates':[a,b,c,d,W],'t':T,'p':p,'G':G,'H':H,'project':[X,Z,W],'wrong_D_mod_p':13,'actual_K_mod_p':0},'second_chart_identity_quotient':str(s.factor(quo)),'exceptional_K_x0':str(s.expand(K.subs({t:-2,x:0})))},indent=2))
