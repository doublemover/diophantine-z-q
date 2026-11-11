module
public import IntegralOriginalProperModel318
public section
noncomputable section
namespace IntegralProperBicanonicalModel318
open AlgebraicGeometry CategoryTheory
open IntegralGluedModel318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The original J² pair now lives on the SAME actual proper separated
integral scheme, with every original branch/infinity restriction retained.
The separation-unit exclusion is unchanged. No regularity, minimality,
semistability or bad-prime extension is asserted. -/
theorem proper_with_original_pair
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsProper (structureMap R c) ∧ IsSeparated (structureMap R c) ∧
    (⊤ ≤ iSup (opens R c)) ∧
    ∃ Q : Fin 2 → Γ(IntegralGluedTensorSections318.tensor R c,⊤),
      Q=q R c hN ∧ ∀ (n : Fin 2) (i : Option (Fin 4)),
        (IntegralGluedTensorSections318.tensor R c).presheaf.map
          (homOfLE (show opens R c i≤⊤ from le_top)).op (Q n)=localQ R c n i := by
  obtain ⟨hp,hs⟩ := IntegralOriginalProperModel318.proper_separated R c
  exact ⟨hp,hs,cover R c hN,q R c hN,rfl,q_restrict R c hN⟩
end IntegralProperBicanonicalModel318
