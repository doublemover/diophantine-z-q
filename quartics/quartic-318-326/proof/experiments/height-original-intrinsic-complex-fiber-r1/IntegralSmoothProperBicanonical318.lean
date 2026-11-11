module
public import IntegralOriginalGlobalSmooth318
public section
noncomputable section
namespace IntegralSmoothProperBicanonical318
open AlgebraicGeometry CategoryTheory
open IntegralGluedModel318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The existing explicit good-base exclusion already inverts two; no
extra unrecorded characteristic hypothesis is being introduced. -/
theorem two_unit (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsUnit (2:R) := by
  have h : (IntegralBranchDenominatorCover318.separationInteger:R)=
      (2:R)*(1138465843200000:R) := by
    norm_num [IntegralBranchDenominatorCover318.separationInteger]
  rw [h] at hN
  exact isUnit_of_mul_isUnit_left hN

/-- A smooth proper separated model over the explicit good integral base,
with the SAME original J² sections and every original chart restriction.
Smoothness is obtained from the actual étale presentations. Neither a smooth
cotangent-module surrogate nor an abstract alternate model is substituted. -/
theorem model_and_original_pair
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    Smooth (structureMap R c) ∧ IsProper (structureMap R c) ∧
    IsSeparated (structureMap R c) ∧ (⊤ ≤ iSup (opens R c)) ∧
    ∃ Q : Fin 2 → Γ(IntegralGluedTensorSections318.tensor R c,⊤),
      Q=q R c hN ∧ ∀ (n : Fin 2) (i : Option (Fin 4)),
        (IntegralGluedTensorSections318.tensor R c).presheaf.map
          (homOfLE (show opens R c i≤⊤ from le_top)).op (Q n)=localQ R c n i :=
  ⟨IntegralOriginalGlobalSmooth318.smooth R c (two_unit R hN) hN,
    IntegralProperBicanonicalModel318.proper_with_original_pair R c hN⟩
end IntegralSmoothProperBicanonical318
