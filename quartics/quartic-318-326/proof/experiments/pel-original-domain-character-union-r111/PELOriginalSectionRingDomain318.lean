module
public import PELOriginalSectionProductNonzero318
public import PELOriginalCubicRelationIdeal318
public import Mathlib.Algebra.Polynomial.Degree.Operations
public section
noncomputable section
namespace PELOriginalSectionRingDomain318
open PELOriginalGradedSectionRing318 PELOriginalSectionMultiplication318
open PELOriginalCubicRelationIdeal318
variable (τ:ℂ)(hτ:0<τ.im)
/-- Genuine leading coefficients lie in their original holomorphic H0
pieces. Their product cannot vanish, even though the surrounding ring of
arbitrary functions DOES have zero divisors. -/
theorem actual_mul_ne_zero(p q:Ring τ hτ)(hp:p≠0)(hq:q≠0):p*q≠0:=by
  have hpv:p.val≠0:=fun h=>hp (Subtype.ext h)
  have hqv:q.val≠0:=fun h=>hq (Subtype.ext h)
  have hl:p.val.leadingCoeff*q.val.leadingCoeff≠0:=
    PELOriginalSectionProductNonzero318.coefficient_product_ne_zero τ hτ
      p.val.natDegree q.val.natDegree _ _ (p.property _) (q.property _)
      (Polynomial.leadingCoeff_ne_zero.mpr hpv) (Polynomial.leadingCoeff_ne_zero.mpr hqv)
  intro h
  have hv:p.val*q.val=0:=congrArg Subtype.val h
  have hc:=congrArg (fun r:Polynomial (Values τ)=>r.coeff (p.val.natDegree+q.val.natDegree)) hv
  rw [Polynomial.coeff_mul_degree_add_degree,Polynomial.coeff_zero] at hc
  exact hl hc
instance actualNoZeroDivisors:NoZeroDivisors (Ring τ hτ) where
  eq_zero_or_eq_zero_of_mul_eq_zero:=by
    intro p q h
    by_cases hp:p=0
    · exact Or.inl hp
    · by_cases hq:q=0
      · exact Or.inr hq
      · exact (actual_mul_ne_zero τ hτ p q hp hq h).elim
instance actualDomain:IsDomain (Ring τ hτ):=NoZeroDivisors.to_isDomain
/-- The actual cubic relations form a PRIME ideal, by evaluation into
the genuine original section ring with its proved no-zero-divisor law.
This is stronger than the earlier cone-point intersection radicality. -/
instance relationsPrime:(relations τ hτ).IsPrime:=
  RingHom.ker_isPrime (presentation τ hτ).toRingHom
/-- The actual homogeneous coordinate quotient is an integral domain;
no projective normality or algebraic/analytic image equality is inferred. -/
instance coordinateDomain:IsDomain (Equations⧸relations τ hτ):=inferInstance
end PELOriginalSectionRingDomain318
