module
public import IntegralPencilLineComparisonData318
public import ModuleTopMorphisms318
public section
noncomputable section
namespace IntegralPencilLineComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

/-- The actual global pullback-O(1) isomorphism to the intrinsic tensor square,
glued from the exact coordinate relations on the complete five-chart cover. -/
@[expose] def iso : IntegralPencilPulledCoordinates318.line R c hN ≅ IntegralGlobalBicanonicalPair318.tensor R c :=
  SectionGeneratedGluing318.iso (IntegralGlobalBicanonicalPair318.opens R c)
    (IntegralPencilLineComparisonData318.pulled R c hN) (IntegralPencilLineComparisonData318.tensor R c hN)
    (IntegralPencilLineComparisonData318.pulled_bijective R c hN) (IntegralPencilLineComparisonData318.tensor_bijective R c hN)
    (IntegralPencilLineComparisonData318.coefficient_relation R c hN) (IntegralGlobalBicanonicalPair318.cover R c hN)

/-- The first actual pulled coordinate morphism maps to the actual q0 morphism. -/
theorem zero_morphism : IntegralPencilPulledCoordinates318.zeroMap R c hN ≫ (iso R c hN).hom=
    IntegralGeneratedTensorSheaf318.sectionMap R c hN 0 :=
  SectionGeneratedGluing318.iso_preserves (IntegralGlobalBicanonicalPair318.opens R c)
    (IntegralPencilLineComparisonData318.pulled R c hN) (IntegralPencilLineComparisonData318.tensor R c hN)
    (IntegralPencilLineComparisonData318.pulled_bijective R c hN) (IntegralPencilLineComparisonData318.tensor_bijective R c hN)
    (IntegralPencilLineComparisonData318.coefficient_relation R c hN) (IntegralGlobalBicanonicalPair318.cover R c hN) (some 0)

/-- The second actual pulled coordinate morphism maps to the actual q1 morphism. -/
theorem one_morphism : IntegralPencilPulledCoordinates318.oneMap R c hN ≫ (iso R c hN).hom=
    IntegralGeneratedTensorSheaf318.sectionMap R c hN 1 :=
  SectionGeneratedGluing318.iso_preserves (IntegralGlobalBicanonicalPair318.opens R c)
    (IntegralPencilLineComparisonData318.pulled R c hN) (IntegralPencilLineComparisonData318.tensor R c hN)
    (IntegralPencilLineComparisonData318.pulled_bijective R c hN) (IntegralPencilLineComparisonData318.tensor_bijective R c hN)
    (IntegralPencilLineComparisonData318.coefficient_relation R c hN) (IntegralGlobalBicanonicalPair318.cover R c hN) none

/-- Scalar-one equality of the literal global first coordinate section. -/
theorem q0_normalized : (iso R c hN).hom.app ⊤ (IntegralPencilPulledCoordinates318.q0 R c hN)=
    IntegralGlobalBicanonicalPair318.q R c hN 0 := by
  have h := congrArg (fun f : SectionGeneratedGluing318.unit (IntegralGluedModel318.scheme R c) ⟶
      IntegralGlobalBicanonicalPair318.tensor R c =>
      f.app ⊤ (show Γ(IntegralGluedModel318.scheme R c,⊤) from 1)) (zero_morphism R c hN)
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)

/-- Scalar-one equality of the literal global second coordinate section. -/
theorem q1_normalized : (iso R c hN).hom.app ⊤ (IntegralPencilPulledCoordinates318.q1 R c hN)=
    IntegralGlobalBicanonicalPair318.q R c hN 1 := by
  have h := congrArg (fun f : SectionGeneratedGluing318.unit (IntegralGluedModel318.scheme R c) ⟶
      IntegralGlobalBicanonicalPair318.tensor R c =>
      f.app ⊤ (show Γ(IntegralGluedModel318.scheme R c,⊤) from 1)) (one_morphism R c hN)
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)

end IntegralPencilLineComparison318
