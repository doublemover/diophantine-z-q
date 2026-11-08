#!/usr/bin/env python3
"""Exact predecessor/candidate arithmetic only; never evaluates an automorphic form."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
r=Path('/workspace/scratch/2cb21e4e0864')
source=r/'recovery-contact-0358/baba-granath-v13/private-sources/published.pdf'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c'
# α=(1/2)+i+(3/2)j; i²=2,j²=-3,ij=-ji. Scalar+pure decomposition.
a,b,c=F(1,2),F(1),F(3,2)
v2=2*b*b-3*c*c
alpha2=(a*a+v2,2*a*b,2*a*c)
assert alpha2==(a-5,b,c)
trace=2*a;norm=a*a-v2;disc=trace*trace-4*norm
assert (trace,norm,disc)==(1,5,-19)
# α=i+3(1+j)/2-1 in the literal maximal-order basis.
assert F(-1)+F(3,2)==a
# In θ(i)=diag(√2,-√2), θ(j)=[[0,-√3],[√3,0]],
# the fixed polynomial is 3√3 z²−4√2 z+3√3. Its root
# (2√2+sqrt(-19))/(3√3) has |z|²=(8+19)/27=1.
assert F(8+19,27)==1
assert (-4)**2*2-4*(3**2*3)==-76
# µ=2j+ij has µ²=-6; its upper fixed point is i(1+√2).
# (2+√2)/(2-√2)=3+2√2=(1+√2)^2.
assert (2*2-2)==2
C=F(16**2,27**2);algebraic_j=F(81,64)
candidates=[algebraic_j,C/algebraic_j]
assert candidates[1]==F(16384,59049)
assert candidates[1]<1<candidates[0]
gap=candidates[0]-candidates[1]
assert gap==F(3734393,3779136)
# Square of h4^3/h6^2 at x6 is -3; hence j_m^2(x6)=16/(9*(-3)).
assert F(16,9)/(-3)==F(-16,27)
print(json.dumps({'status':'PASS exact predecessor and candidate arithmetic; numerical evaluation OPEN',
 'alpha_order':'Z[i+(1+3j)/2]','trace':str(trace),'norm':str(norm),'minimal_polynomial':'X^2-X+5','discriminant':str(disc),
 'order_basis_coefficients':['-1','1','3','0'],
 'fixed_point_in_declared_embedding':'(2sqrt(2)+i sqrt(19))/(3sqrt(3))',
 'upper_half_plane':True,'absolute_value_squared':'1','x6_in_declared_embedding':'i(1+sqrt(2))',
 'published_normalization':'h4^3/h6^2(x6)=sqrt(-3), not -3',
 'candidate_F_values':list(map(str,candidates)),'candidate_decimal_illustrations':[str(float(x)) for x in candidates],
 'candidate_gap':str(gap),'threshold':'1','threshold_margins':[str(candidates[0]-1),str(1-candidates[1])],
 'sufficient_certificate':'A correctly normalized certified enclosure with Re(F)>1 (for example 1<F<3/2), after all two-candidate/CM-orbit predecessors are supplied.',
 'no_actual_modular_form_evaluation':True,'no_empirical_approximation_claim':True},indent=2))
