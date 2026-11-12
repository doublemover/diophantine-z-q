module
public import OriginalGoodPlaceCotangentNorms318
public section
noncomputable section
namespace OriginalGoodNormSupport318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
include hn in
theorem coordinate_ne : t≠0 := by
  intro h
  apply hn 0
  rw [RationalContactPoint318.parameters_eq,h]
  norm_num [LinearContactSquareclass318.contacts]

theorem second_value_ne : ContactBicanonicalPointHeight318.a1 c t hn i≠0 := by
  rw [ContactBicanonicalPointHeight318.ratio]
  exact mul_ne_zero (by exact_mod_cast coordinate_ne c t hn) (ContactBicanonicalPointHeight318.a0_ne c t hn i)

/-- Finite support on the actual good-place domain is proved from the
original nonzero section values. No value is assigned to excluded bad
places merely to manufacture a global adelic metric. -/
theorem finite_support :
    ∃ S : Set (FinitePlace (K c t)), S.Finite ∧
      ∀ (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1),
        v ∉ S → OriginalGoodPlaceCotangentNorms318.finiteNorm c t hn v hv i=1 := by
  let S0 := {v : FinitePlace (K c t) | v (ContactBicanonicalPointHeight318.a0 c t hn i)≠1}
  let S1 := {v : FinitePlace (K c t) | v (ContactBicanonicalPointHeight318.a1 c t hn i)≠1}
  have h0 : S0.Finite := FinitePlace.hasFiniteMulSupport (ContactBicanonicalPointHeight318.a0_ne c t hn i)
  have h1 : S1.Finite := FinitePlace.hasFiniteMulSupport (second_value_ne c t hn i)
  refine ⟨S0∪S1,h0.union h1,?_⟩
  intro v hv hs
  have hv0 : v (ContactBicanonicalPointHeight318.a0 c t hn i)=1 := by
    by_contra h
    exact hs (Or.inl h)
  have hv1 : v (ContactBicanonicalPointHeight318.a1 c t hn i)=1 := by
    by_contra h
    exact hs (Or.inr h)
  rw [OriginalGoodPlaceCotangentNorms318.finiteNorm_eq_max_inverse,hv0,hv1,max_self,inv_one]
end OriginalGoodNormSupport318
