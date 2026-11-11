module
public import CompactPeriodicHolomorphicQuotient318
public import PELOriginalThetaZeroComplexPoints318
public import PELOriginalEntireTranslationCharacter318
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public section
noncomputable section
namespace PELOriginalThetaHasZero318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalPeriodLattice318 PELOriginalPolarizationAutomorphy318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance periodsDiscrete : DiscreteTopology (periodSubgroup representation order τ) := original_discrete τ hτ
local instance originalCompact : CompactSpace (PeriodQuotient representation order τ) := original_compact τ hτ

/-- If original theta were everywhere nonzero, all original cubic theta
functions would be scalar multiples of its cube by compactness and
Liouville. This contradicts their independently proved independence. -/
theorem exists_zero : ∃ z : ComplexVectors,value τ hτ 1 (0 : Label 1) z=0 := by
  classical
  by_contra h
  push_neg at h
  let d : ComplexVectors → ℂ := fun z => value τ hτ 1 (0 : Label 1) z^3
  have hd : Differentiable ℂ d := (holomorphic τ hτ 1 (0 : Label 1)).pow 3
  have hn (z : ComplexVectors) : d z≠0 := pow_ne_zero 3 (h z)
  have hm (r : Label 3) : ∃ c : ℂ,∀ z,value τ hτ 3 r z=c*d z := by
    apply CompactPeriodicHolomorphicQuotient318.quotient_constant
      (periodSubgroup representation order τ) (value τ hτ 3 r) d
      (holomorphic τ hτ 3 r) hd hn
    intro l z
    have hl : l.val∈L τ hτ := by
      change l.val∈lattice τ hτ
      rw [←exact_period_subgroup τ hτ]
      exact l.property
    rw [d,original_automorphy τ hτ 3 r ⟨l.val,hl⟩ z,
      original_automorphy τ hτ 1 (0 : Label 1) ⟨l.val,hl⟩ z,pow_one,mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero 3 (nonzero τ hτ ⟨l.val,hl⟩ z))
  let k : Fin 2 → Label 3 := fun i => ((i.val : ZMod 3),0)
  have hk : Function.Injective k := by
    intro i j he
    fin_cases i <;> fin_cases j <;> norm_num [k] at he ⊢
  have hi : LinearIndependent ℂ (fun i : Fin 2 => value τ hτ 3 (k i)) :=
    (original_values_independent τ hτ 3).comp k hk
  obtain ⟨a,ha⟩ := hm (k 0)
  obtain ⟨b,hb⟩ := hm (k 1)
  have hb0 : b≠0 := by
    intro hz
    apply hi.ne_zero 1
    funext z
    simpa only [hz,zero_mul] using hb z
  apply (linearIndependent_fin2.mp hi).2 (a/b)
  funext z
  change (a/b)*value τ hτ 3 (k 1) z=value τ hτ 3 (k 0) z
  rw [ha,hb]
  field_simp [hb0]

/-- The actual theta zero scheme is nonempty, via a produced original
zero and its genuine Spec(C)-valued lift, not a postulated divisor point. -/
instance zeroScheme_nonempty : Nonempty (PELOriginalThetaZeroScheme318.zeroScheme τ hτ) := by
  obtain ⟨z,hz⟩ := exists_zero τ hτ
  exact ⟨PELOriginalThetaZeroComplexPoints318.originalPoint τ hτ z hz (IsLocalRing.closedPoint ℂ)⟩
end PELOriginalThetaHasZero318
