module
public import ContactLineComparisonData318
public import ContactLocalLineComparison318
public section
noncomputable section
namespace ContactGlobalLineComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The actual global pullback-O(1) isomorphism to the intrinsic tensor square,
glued from the exact coordinate relations on the complete five-chart cover. -/
@[expose] def iso : ContactProjectiveLinePullback318.line c ≅ ContactGlobalBicanonical318.tensor c :=
  SectionGeneratedGluing318.iso (ContactGlobalBicanonical318.opens c)
    (ContactLineComparisonData318.pulled c) (ContactLineComparisonData318.tensor c)
    (ContactLineComparisonData318.pulled_bijective c) (ContactLineComparisonData318.tensor_bijective c)
    (ContactLineComparisonData318.coefficient_relation c) (ContactGlobalBicanonical318.cover c)

/-- The first actual pulled coordinate morphism maps to the actual q0 morphism. -/
theorem zero_morphism : ContactPulledCoordinates318.zeroMap c ≫ (iso c).hom=
    ContactBicanonicalSheafMaps318.zeroMap c :=
  SectionGeneratedGluing318.iso_preserves (ContactGlobalBicanonical318.opens c)
    (ContactLineComparisonData318.pulled c) (ContactLineComparisonData318.tensor c)
    (ContactLineComparisonData318.pulled_bijective c) (ContactLineComparisonData318.tensor_bijective c)
    (ContactLineComparisonData318.coefficient_relation c) (ContactGlobalBicanonical318.cover c) (some 0)

/-- The second actual pulled coordinate morphism maps to the actual q1 morphism. -/
theorem one_morphism : ContactPulledCoordinates318.oneMap c ≫ (iso c).hom=
    ContactBicanonicalSheafMaps318.oneMap c :=
  SectionGeneratedGluing318.iso_preserves (ContactGlobalBicanonical318.opens c)
    (ContactLineComparisonData318.pulled c) (ContactLineComparisonData318.tensor c)
    (ContactLineComparisonData318.pulled_bijective c) (ContactLineComparisonData318.tensor_bijective c)
    (ContactLineComparisonData318.coefficient_relation c) (ContactGlobalBicanonical318.cover c) none

/-- Scalar-one equality of the literal global first coordinate section. -/
theorem q0_normalized : (iso c).hom.app ⊤ (ContactPulledCoordinates318.q0 c)=
    ContactGlobalBicanonical318.q0 c := by
  have h := congrArg (fun f : SectionGeneratedGluing318.unit (ContactGlobalSmooth318.Model c) ⟶
      ContactGlobalBicanonical318.tensor c =>
      f.app ⊤ (show Γ(ContactGlobalSmooth318.Model c,⊤) from 1)) (zero_morphism c)
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)

/-- Scalar-one equality of the literal global second coordinate section. -/
theorem q1_normalized : (iso c).hom.app ⊤ (ContactPulledCoordinates318.q1 c)=
    ContactGlobalBicanonical318.q1 c := by
  have h := congrArg (fun f : SectionGeneratedGluing318.unit (ContactGlobalSmooth318.Model c) ⟶
      ContactGlobalBicanonical318.tensor c =>
      f.app ⊤ (show Γ(ContactGlobalSmooth318.Model c,⊤) from 1)) (one_morphism c)
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)

/-- The global comparison restricts to the previously proved, exact finite comparison. -/
theorem branch_comparison (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).mapIso (iso c)=
      ContactLocalLineComparison318.branchIso c i := by
  apply Iso.ext
  letI := ContactPulledCoordinates318.zero_branch_isIso c i
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
    (ContactPulledCoordinates318.zeroMap c))).mp
  change (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
    (ContactPulledCoordinates318.zeroMap c) ≫
      (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map (iso c).hom=_
  rw [←Functor.map_comp,zero_morphism]
  exact (ContactLocalLineComparison318.branch_normalized c i).symm

/-- The global comparison restricts to the previously proved, exact infinity comparison. -/
theorem infinity_comparison :
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).mapIso (iso c)=
      ContactLocalLineComparison318.infinityIso c := by
  apply Iso.ext
  letI := ContactPulledCoordinates318.one_infinity_isIso c
  apply (cancel_epi ((Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
    (ContactPulledCoordinates318.oneMap c))).mp
  change (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
    (ContactPulledCoordinates318.oneMap c) ≫
      (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map (iso c).hom=_
  rw [←Functor.map_comp,one_morphism]
  exact (ContactLocalLineComparison318.infinity_normalized c).symm
end ContactGlobalLineComparison318
