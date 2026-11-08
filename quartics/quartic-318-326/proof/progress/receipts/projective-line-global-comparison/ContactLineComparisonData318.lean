module
public import ContactPulledRatios318
public import RestrictedMapBijective318
public import RestrictionScalarRelation318
public import ContactBicanonicalSheafMaps318
public section
noncomputable section
namespace ContactLineComparisonData318
open AlgebraicGeometry CategoryTheory Opposite
open SectionGeneratedGluing318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
@[expose] def pulled : Option (Fin 4) →
    (unit (ContactGlobalSmooth318.Model c) ⟶ ContactProjectiveLinePullback318.line c)
  | some _ => ContactPulledCoordinates318.zeroMap c
  | none => ContactPulledCoordinates318.oneMap c
@[expose] def tensor : Option (Fin 4) →
    (unit (ContactGlobalSmooth318.Model c) ⟶ ContactGlobalBicanonical318.tensor c)
  | some _ => ContactBicanonicalSheafMaps318.zeroMap c
  | none => ContactBicanonicalSheafMaps318.oneMap c

theorem pulled_bijective (i : Option (Fin 4)) (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V≤ContactGlobalBicanonical318.opens c i) :
    Function.Bijective (genLinear (pulled c i) V) := by
  cases i with
  | some i =>
    letI := ContactPulledCoordinates318.zero_branch_isIso c i
    exact RestrictedMapBijective318.bijective (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactPulledCoordinates318.zeroMap c) V hV
  | none =>
    letI := ContactPulledCoordinates318.one_infinity_isIso c
    exact RestrictedMapBijective318.bijective (InfinityGlobalScheme318.chartEmbedding c)
      (ContactPulledCoordinates318.oneMap c) V hV

theorem tensor_bijective (i : Option (Fin 4)) (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V≤ContactGlobalBicanonical318.opens c i) :
    Function.Bijective (genLinear (tensor c i) V) := by
  cases i with
  | some i =>
    letI := ContactBicanonicalSheafMaps318.zero_branch_isIso c i
    exact RestrictedMapBijective318.bijective (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactBicanonicalSheafMaps318.zeroMap c) V hV
  | none =>
    letI := ContactBicanonicalSheafMaps318.one_infinity_isIso c
    exact RestrictedMapBijective318.bijective (InfinityGlobalScheme318.chartEmbedding c)
      (ContactBicanonicalSheafMaps318.oneMap c) V hV

/-- All indexed generator pairs have the very same exact ambient coefficient,
on every full chart. The distinct finite charts all choose the same q0. -/
theorem coefficient_relation (i j : Option (Fin 4)) :
    ∃ a : Γ(ContactGlobalSmooth318.Model c,ContactGlobalBicanonical318.opens c i),
      genLinear (pulled c j) (ContactGlobalBicanonical318.opens c i) 1=
        a • genLinear (pulled c i) (ContactGlobalBicanonical318.opens c i) 1 ∧
      genLinear (tensor c j) (ContactGlobalBicanonical318.opens c i) 1=
        a • genLinear (tensor c i) (ContactGlobalBicanonical318.opens c i) 1 := by
  cases i with
  | some i =>
    cases j with
    | some j => exact ⟨1,by simp only [pulled,one_smul],by simp only [tensor,one_smul]⟩
    | none =>
      refine ⟨ContactBicanonicalSectionRatios318.branchRatioSection c i,?_,?_⟩
      · exact RestrictionScalarRelation318.top_value
          (ContactIntrinsicFrames318.branchEmbedding c i)
          (ContactPulledCoordinates318.zeroMap c) (ContactPulledCoordinates318.oneMap c)
          ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
            (ContactBicanonicalRatios318.branchRatio c i)) (ContactPulledRatios318.branch_relation c i)
      · change (ModuleGlobalSections318.ofTop _ (ContactGlobalBicanonical318.q1 c)).val.app
          (op (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)) (show Γ(ContactGlobalSmooth318.Model c,
            ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) from 1)=
          ContactBicanonicalSectionRatios318.branchRatioSection c i •
          (ModuleGlobalSections318.ofTop _ (ContactGlobalBicanonical318.q0 c)).val.app
          (op (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)) (show Γ(ContactGlobalSmooth318.Model c,
            ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) from 1)
        rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one]
        exact ContactBicanonicalSectionRatios318.global_branch_relation c i
  | none =>
    cases j with
    | none => exact ⟨1,by simp only [pulled,one_smul],by simp only [tensor,one_smul]⟩
    | some j =>
      refine ⟨ContactBicanonicalSectionRatios318.infinityRatioSection c,?_,?_⟩
      · exact RestrictionScalarRelation318.top_value
          (InfinityGlobalScheme318.chartEmbedding c)
          (ContactPulledCoordinates318.oneMap c) (ContactPulledCoordinates318.zeroMap c)
          ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
            (ContactBicanonicalRatios318.infinityRatio c)) (ContactPulledRatios318.infinity_relation c)
      · change (ModuleGlobalSections318.ofTop _ (ContactGlobalBicanonical318.q0 c)).val.app
          (op (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤)) (show Γ(ContactGlobalSmooth318.Model c,
            InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) from 1)=
          ContactBicanonicalSectionRatios318.infinityRatioSection c •
          (ModuleGlobalSections318.ofTop _ (ContactGlobalBicanonical318.q1 c)).val.app
          (op (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤)) (show Γ(ContactGlobalSmooth318.Model c,
            InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) from 1)
        rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one]
        exact ContactBicanonicalSectionRatios318.global_infinity_relation c
end ContactLineComparisonData318
