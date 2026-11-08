module
public import ContactPulledCoordinates318
public import ContactBicanonicalSheafMaps318
public section
noncomputable section
namespace ContactLocalLineComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
/-- The actual source line sheaves are compared on the whole finite chart
by carrying the literal pulled coordinate to the literal bicanonical section. -/
@[expose] def branchIso (i : Fin 4) :
    (ContactProjectiveLinePullback318.line c).restrict (ContactIntrinsicFrames318.branchEmbedding c i) ≅
      (ContactGlobalBicanonical318.tensor c).restrict (ContactIntrinsicFrames318.branchEmbedding c i) := by
  letI := ContactPulledCoordinates318.zero_branch_isIso c i
  letI := ContactBicanonicalSheafMaps318.zero_branch_isIso c i
  exact (asIso ((Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
    (ContactPulledCoordinates318.zeroMap c))).symm ≪≫
    asIso ((Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (ContactBicanonicalSheafMaps318.zeroMap c))

/-- The whole infinity-chart comparison carries the literal second coordinates. -/
@[expose] def infinityIso :
    (ContactProjectiveLinePullback318.line c).restrict (InfinityGlobalScheme318.chartEmbedding c) ≅
      (ContactGlobalBicanonical318.tensor c).restrict (InfinityGlobalScheme318.chartEmbedding c) := by
  letI := ContactPulledCoordinates318.one_infinity_isIso c
  letI := ContactBicanonicalSheafMaps318.one_infinity_isIso c
  exact (asIso ((Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
    (ContactPulledCoordinates318.oneMap c))).symm ≪≫
    asIso ((Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactBicanonicalSheafMaps318.oneMap c))

theorem branch_normalized (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (ContactPulledCoordinates318.zeroMap c) ≫ (branchIso c i).hom=
    (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (ContactBicanonicalSheafMaps318.zeroMap c) := by
  simp [branchIso]

theorem infinity_normalized :
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactPulledCoordinates318.oneMap c) ≫ (infinityIso c).hom=
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactBicanonicalSheafMaps318.oneMap c) := by
  simp [infinityIso]
end ContactLocalLineComparison318
