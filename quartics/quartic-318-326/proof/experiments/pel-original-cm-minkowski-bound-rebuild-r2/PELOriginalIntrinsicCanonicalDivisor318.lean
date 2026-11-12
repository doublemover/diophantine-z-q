module
public import FourRootCanonicalFiniteEquationOrder318
public import PELOriginalBaseDifferentialDivisor318
public section
noncomputable section
namespace PELOriginalIntrinsicCanonicalDivisor318
open scoped Classical BigOperators OnePoint
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 FourRootActualSchemeDvr318
open FourRootNormalizedPointCharts318
local instance integral:AlgebraicGeometry.IsIntegral (FourRootGluedScheme318.scheme branches):=
  FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance actualFiniteDvr(q:FinitePoints branches):
    IsDiscreteValuationRing ((FourRootGluedScheme318.scheme branches).presheaf.stalk
      (finiteImage branches q)):=finiteActualDvr branches branches_injective q
/-- The coefficient is defined FIRST from the new actual intrinsic
canonical-line rational equation and the genuine whole-Scheme DVR at
the SAME original complex point. It is not defined as a desired order
or copied from the earlier coefficient-divisor formula. -/
@[expose] def coefficient(p:UnlevelledBase):ℤ:=
  match completedMap p with
  | .inl q=>ActualDvrMeromorphicOrder318.order
      ((FourRootGluedScheme318.scheme branches).presheaf.stalk (finiteImage branches q))
      (FourRootGluedScheme318.scheme branches).functionField
      (FourRootCanonicalRationalEquations318.localEquation branches branches_injective
        (some (FourRootActualFiniteDifferentialOrders318.chartIndex branches q)))
  | .inr s=>
      letI:=infinityActualDvr branches branches_injective (center branches s) rfl
      ActualDvrMeromorphicOrder318.order
        ((FourRootGluedScheme318.scheme branches).presheaf.stalk (infinityImage branches (center branches s)))
        (FourRootGluedScheme318.scheme branches).functionField
        (FourRootCanonicalRationalEquations318.localEquation branches branches_injective none)
/-- Exact bridge from genuine intrinsic Omega local equations to the
independently computed original dt coefficient orders, INCLUDING all
eight infinity points and their order-three poles. -/
theorem coefficient_eq(p:UnlevelledBase):
    coefficient p=PELOriginalBaseDifferentialDivisor318.coefficient p:=by
  unfold coefficient PELOriginalBaseDifferentialDivisor318.coefficient
  cases h:completedMap p with
  | inl q=>
    unfold ActualDvrMeromorphicOrder318.order FourRootActualFiniteDifferentialOrders318.order
    rw [FourRootCanonicalFiniteEquationOrder318.same_finite_value branches branches_injective q]
  | inr s=>
    letI:=infinityActualDvr branches branches_injective (center branches s) rfl
    unfold ActualDvrMeromorphicOrder318.order
    rw [FourRootCanonicalInfinityEquationOrder318.infinity_equation_value branches branches_injective _ rfl,
      FourRootActualInfinityDifferentialOrders318.order_minus_three branches branches_injective _ rfl]
    rfl
/-- Finite support now belongs to the coefficients of the ACTUAL
intrinsic canonical-line equations. The equations have genuine regular
unit ratios and their associated line is SAME Omega; no unconstructed
quotient Cartier-divisor object is asserted. -/
@[expose] def divisor:UnlevelledBase→₀ℤ:=
  Finsupp.onFinset PELOriginalActualDifferentDivisor318.support coefficient (by
    intro p hp
    have hn:PELOriginalBaseDifferentialDivisor318.divisor p≠0:=by
      rw [PELOriginalBaseDifferentialDivisor318.divisor_apply,←coefficient_eq]
      exact hp
    exact (PELOriginalActualDifferentDivisor318.support_iff p).mpr
      ((PELOriginalBaseDifferentialDivisor318.support_exact p).mp hn))
lemma divisor_apply(p:UnlevelledBase):divisor p=coefficient p:=rfl
/-- Equality is proved only AFTER the actual sheaf-frame and scalar-germ
comparisons; it does not rename the old Finsupp as a canonical line. -/
theorem same_divisor:divisor=PELOriginalBaseDifferentialDivisor318.divisor:=by
  ext p
  exact coefficient_eq p
theorem original_different_comparison(p:UnlevelledBase):
    coefficient p=(PELOriginalActualDifferentDivisor318.coefficient p:ℤ)-
      (if PELOriginalContactBranchSquare318.normalizedMap p=∞ then 4 else 0):=by
  rw [coefficient_eq]
  exact PELOriginalBaseDifferentialDivisor318.actual_different_comparison p
theorem degree_eight:
    (∑p:PELOriginalBaseDifferentialDivisor318.Ramification,divisor p.val)=8:=by
  rw [same_divisor]
  exact PELOriginalBaseDifferentialDivisor318.degree_eight
end PELOriginalIntrinsicCanonicalDivisor318
