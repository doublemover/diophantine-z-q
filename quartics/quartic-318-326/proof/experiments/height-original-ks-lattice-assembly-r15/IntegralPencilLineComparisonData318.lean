module
public import IntegralPencilPulledRatios318
public import RestrictedMapBijective318
public import RestrictionScalarRelation318
public import IntegralGeneratedTensorSheaf318
public section
noncomputable section
namespace IntegralPencilLineComparisonData318
open AlgebraicGeometry CategoryTheory Opposite
open SectionGeneratedGluing318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
@[expose] def pulled : Option (Fin 4) →
    (unit (IntegralGluedModel318.scheme R c) ⟶ IntegralPencilPulledCoordinates318.line R c hN)
  | some _ => IntegralPencilPulledCoordinates318.zeroMap R c hN
  | none => IntegralPencilPulledCoordinates318.oneMap R c hN
@[expose] def tensor : Option (Fin 4) →
    (unit (IntegralGluedModel318.scheme R c) ⟶ IntegralGlobalBicanonicalPair318.tensor R c)
  | some _ => IntegralGeneratedTensorSheaf318.sectionMap R c hN 0
  | none => IntegralGeneratedTensorSheaf318.sectionMap R c hN 1

theorem pulled_bijective (i : Option (Fin 4)) (V : (IntegralGluedModel318.scheme R c).Opens)
    (hV : V≤IntegralGlobalBicanonicalPair318.opens R c i) :
    Function.Bijective (genLinear (pulled R c hN i) V) := by
  cases i with
  | some i =>
    letI := IntegralPencilPulledCoordinates318.zero_branch_isIso R c hN i
    exact RestrictedMapBijective318.bijective (IntegralGluedDifferentialFrames318.branchEmbedding R c i)
      (IntegralPencilPulledCoordinates318.zeroMap R c hN) V hV
  | none =>
    letI := IntegralPencilPulledCoordinates318.one_infinity_isIso R c hN
    exact RestrictedMapBijective318.bijective (IntegralGluedModel318.infinityChart R c)
      (IntegralPencilPulledCoordinates318.oneMap R c hN) V hV

theorem tensor_bijective (i : Option (Fin 4)) (V : (IntegralGluedModel318.scheme R c).Opens)
    (hV : V≤IntegralGlobalBicanonicalPair318.opens R c i) :
    Function.Bijective (genLinear (tensor R c hN i) V) := by
  cases i with
  | some i =>
    letI := IntegralGeneratedTensorSheaf318.chart_section_isIso R c hN (some i)
    exact RestrictedMapBijective318.bijective (IntegralGluedDifferentialFrames318.branchEmbedding R c i)
      (IntegralGeneratedTensorSheaf318.sectionMap R c hN 0) V hV
  | none =>
    letI := IntegralGeneratedTensorSheaf318.chart_section_isIso R c hN none
    exact RestrictedMapBijective318.bijective (IntegralGluedModel318.infinityChart R c)
      (IntegralGeneratedTensorSheaf318.sectionMap R c hN 1) V hV

/-- All indexed generator pairs have the very same exact ambient coefficient,
on every full chart. The distinct finite charts all choose the same q0. -/
theorem coefficient_relation (i j : Option (Fin 4)) :
    ∃ a : Γ(IntegralGluedModel318.scheme R c,IntegralGlobalBicanonicalPair318.opens R c i),
      genLinear (pulled R c hN j) (IntegralGlobalBicanonicalPair318.opens R c i) 1=
        a • genLinear (pulled R c hN i) (IntegralGlobalBicanonicalPair318.opens R c i) 1 ∧
      genLinear (tensor R c hN j) (IntegralGlobalBicanonicalPair318.opens R c i) 1=
        a • genLinear (tensor R c hN i) (IntegralGlobalBicanonicalPair318.opens R c i) 1 := by
  cases i with
  | some i =>
    cases j with
    | some j => exact ⟨1,by simp only [pulled,one_smul],by simp only [tensor,one_smul]⟩
    | none =>
      refine ⟨IntegralOriginalSectionRatios318.branchRatio R c i,?_,?_⟩
      · exact RestrictionScalarRelation318.top_value
          (IntegralGluedDifferentialFrames318.branchEmbedding R c i)
          (IntegralPencilPulledCoordinates318.zeroMap R c hN) (IntegralPencilPulledCoordinates318.oneMap R c hN)
          ((Scheme.ΓSpecIso (CommRingCat.of (IntegralBranchCoordinates318.B R c i))).inv
            (IntegralBranchCoordinates318.sourceT R c i)) (IntegralPencilPulledRatios318.branch_relation R c hN i)
      · change (ModuleGlobalSections318.ofTop _ (IntegralGlobalBicanonicalPair318.q R c hN 1)).val.app
          (op (IntegralGluedDifferentialFrames318.branchEmbedding R c i ''ᵁ ⊤)) (show Γ(IntegralGluedModel318.scheme R c,
            IntegralGluedDifferentialFrames318.branchEmbedding R c i ''ᵁ ⊤) from 1)=
          IntegralOriginalSectionRatios318.branchRatio R c i •
          (ModuleGlobalSections318.ofTop _ (IntegralGlobalBicanonicalPair318.q R c hN 0)).val.app
          (op (IntegralGluedDifferentialFrames318.branchEmbedding R c i ''ᵁ ⊤)) (show Γ(IntegralGluedModel318.scheme R c,
            IntegralGluedDifferentialFrames318.branchEmbedding R c i ''ᵁ ⊤) from 1)
        rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one]
        exact IntegralOriginalSectionRatios318.global_branch_relation R c hN i
  | none =>
    cases j with
    | none => exact ⟨1,by simp only [pulled,one_smul],by simp only [tensor,one_smul]⟩
    | some j =>
      refine ⟨IntegralOriginalSectionRatios318.infinityRatio R c,?_,?_⟩
      · exact RestrictionScalarRelation318.top_value
          (IntegralGluedModel318.infinityChart R c)
          (IntegralPencilPulledCoordinates318.oneMap R c hN) (IntegralPencilPulledCoordinates318.zeroMap R c hN)
          ((Scheme.ΓSpecIso (CommRingCat.of (IntegralInfinityChart318.Order R c))).inv
            (IntegralOriginalContactPencil318.infinityRatioValue R c)) (IntegralPencilPulledRatios318.infinity_relation R c hN)
      · change (ModuleGlobalSections318.ofTop _ (IntegralGlobalBicanonicalPair318.q R c hN 0)).val.app
          (op (IntegralGluedModel318.infinityChart R c ''ᵁ ⊤)) (show Γ(IntegralGluedModel318.scheme R c,
            IntegralGluedModel318.infinityChart R c ''ᵁ ⊤) from 1)=
          IntegralOriginalSectionRatios318.infinityRatio R c •
          (ModuleGlobalSections318.ofTop _ (IntegralGlobalBicanonicalPair318.q R c hN 1)).val.app
          (op (IntegralGluedModel318.infinityChart R c ''ᵁ ⊤)) (show Γ(IntegralGluedModel318.scheme R c,
            IntegralGluedModel318.infinityChart R c ''ᵁ ⊤) from 1)
        rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one]
        exact IntegralOriginalSectionRatios318.global_infinity_relation R c hN
end IntegralPencilLineComparisonData318
