module
public import PELOriginalMultiplicationFourierFormula318
public import Mathlib.Analysis.Complex.Liouville
public section
noncomputable section
namespace PELOriginalSectionDegreeZero318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalWholeHZeroDimension318
open PELOriginalPowerSectionLift318 PELOriginalSectionMultiplication318
open Set
variable (τ:ℂ)(hτ:0<τ.im)
local instance sourceCompact:CompactSpace (Base τ):=
  PELComplexPeriodSurface318.surface_compact τ hτ
lemma zero_lift(s:homogeneous τ hτ 0)(z:ComplexVectors):
    lift τ hτ 0 (asSection τ hτ 0 s) z=s.val (projection (P τ) z):=by
  simp only [lift,gauge,pow_zero,inv_one,one_mul,asSection]
lemma coefficient_continuous(s:homogeneous τ hτ 0):Continuous s.val:=by
  have hp:IsQuotientMap (projection (P τ)):=isQuotientMap_quotient_mk'
  apply hp.continuous_iff.mpr
  have he:s.val∘projection (P τ)=lift τ hτ 0 (asSection τ hτ 0 s):=by
    funext z
    exact (zero_lift τ hτ s z).symm
  rw [he]
  exact (PELOriginalPowerSectionLift318.entire τ hτ 0 (asSection τ hτ 0 s)).continuous

/-- Degree zero is genuinely the constants: an arbitrary original
holomorphic section descends continuously on the ACTUAL compact torus;
its actual entire lift is bounded and Liouville applies. No finite-
dimensionality, theta-span or algebraization premise is used. -/
theorem degree_zero_constant(s:homogeneous τ hτ 0)(q:Base τ):
    s.val q=s.val (projection (P τ) 0):=by
  have hc:=coefficient_continuous τ hτ s
  have hb:Bornology.IsBounded (Set.range (lift τ hτ 0 (asSection τ hτ 0 s))):=by
    apply (isCompact_range hc).isBounded.subset
    rintro y ⟨z,rfl⟩
    exact ⟨projection (P τ) z,(zero_lift τ hτ s z).symm⟩
  obtain ⟨z,rfl⟩:=quotient_surjective (P τ) q
  simpa only [zero_lift] using
    (PELOriginalPowerSectionLift318.entire τ hτ 0 (asSection τ hτ 0 s)).apply_eq_apply_of_bounded hb z 0

@[expose] def evaluation:homogeneous τ hτ 0→ₗ[ℂ]ℂ where
  toFun s:=s.val (projection (P τ) 0)
  map_add' s t:=rfl
  map_smul' c s:=rfl
@[expose] def constants:ℂ→ₗ[ℂ]homogeneous τ hτ 0 where
  toFun c:=⟨fun _=>c,constant_mem τ hτ c⟩
  map_add' c d:=rfl
  map_smul' c d:=rfl
@[expose] def degreeZeroEquivalence:homogeneous τ hτ 0≃ₗ[ℂ]ℂ where
  __:=evaluation τ hτ
  invFun:=constants τ hτ
  left_inv s:=by
    apply Subtype.ext
    funext q
    exact (degree_zero_constant τ hτ s q).symm
  right_inv c:=rfl
instance zero_finiteDimensional:FiniteDimensional ℂ (homogeneous τ hτ 0):=
  FiniteDimensional.of_injective (evaluation τ hτ) (degreeZeroEquivalence τ hτ).injective

/-- The actual full graded H0 Hilbert function, including its proved
constant degree zero. This is not asserted to be an algebraic Hilbert
polynomial until a genuine algebraic identification is constructed. -/
theorem whole_hilbert_function(N:ℕ):
    Module.finrank ℂ (homogeneous τ hτ N)=if N=0 then 1 else N^2:=by
  by_cases hN:N=0
  · subst N
    rw [(degreeZeroEquivalence τ hτ).finrank_eq]
    simp
  · letI:NeZero N:=⟨hN⟩
    rw [if_neg hN]
    exact actual_hzero_dimension τ hτ N
end PELOriginalSectionDegreeZero318
