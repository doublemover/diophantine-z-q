module
public import IntegralRationalGlobalComparison318
public import IntegralRationalBranchCoefficients318
public import IntegralRationalInfinityCoefficients318
public section
noncomputable section
namespace IntegralRationalFiveChartGeometry318
open AlgebraicGeometry CategoryTheory
open IntegralRationalGlobalComparison318 IntegralRationalFiniteAtlas318
open IntegralGluedModel318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def branchIso (i : Fin 4) :
    Spec (CommRingCat.of (IntegralBranchCoordinates318.B ℚ c i)) ≅
    Spec (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i)) :=
  Scheme.Spec.mapIso (branchEquiv c i).toRingEquiv.toCommRingCatIso.symm.op

theorem branch_inverse_square (i : Fin 4) :
    (branchIso c i).inv ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (IntegralSourceBranches318.SourceOrder ℚ c) (IntegralBranchCoordinates318.B ℚ c i))) =
    Spec.map (CommRingCat.ofHom
      (algebraMap (ContactKummerOrder318.SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i))) ≫
      (finiteIso c).inv := by
  change Spec.map (branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫ _ = _
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact branchEquiv_source c i

theorem branch_square (i : Fin 4) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (IntegralSourceBranches318.SourceOrder ℚ c) (IntegralBranchCoordinates318.B ℚ c i))) ≫
        (finiteIso c).hom =
    (branchIso c i).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ContactKummerOrder318.SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i))) := by
  apply (cancel_epi (branchIso c i).inv).mp
  rw [←Category.assoc,branch_inverse_square]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

/-- Every one of the four integral branch charts reaches its original
rational chart through the actual global comparison, with no chart permutation. -/
theorem branch_toOriginal (i : Fin 4) :
    IntegralGluedDifferentialFrames318.branchEmbedding ℚ c i ≫ toOriginal c =
      (branchIso c i).hom ≫ ContactIntrinsicFrames318.branchEmbedding c i := by
  unfold IntegralGluedDifferentialFrames318.branchEmbedding ContactIntrinsicFrames318.branchEmbedding
  rw [Category.assoc,finite_toOriginal,←Category.assoc,branch_square,Category.assoc]

/-- The integral charts, viewed through the original model isomorphism,
are actual affine open charts of the original normalization. -/
@[expose] def branchEmbedding (i : Fin 4) :=
  IntegralGluedDifferentialFrames318.branchEmbedding ℚ c i ≫ toOriginal c
@[expose] def infinityEmbedding := infinityChart ℚ c ≫ toOriginal c
instance branch_open (i : Fin 4) : IsOpenImmersion (branchEmbedding c i) := by
  change IsOpenImmersion (IntegralGluedDifferentialFrames318.branchEmbedding ℚ c i ≫
    (originalModelIso c).hom)
  infer_instance
instance infinity_open : IsOpenImmersion (infinityEmbedding c) := by
  change IsOpenImmersion (infinityChart ℚ c ≫ (originalModelIso c).hom)
  infer_instance

theorem branch_structure (i : Fin 4) :
    branchEmbedding c i ≫ ContactIntrinsicDifferentials318.structureMap c =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (IntegralBranchCoordinates318.B ℚ c i))) := by
  change (IntegralGluedDifferentialFrames318.branchEmbedding ℚ c i ≫ toOriginal c) ≫
    ((ContactProjectiveModel318.coverMap c).fromNormalization ≫ ProjectiveJLine318.structureMap ℚ) = _
  rw [Category.assoc,over_Q]
  exact IntegralGluedDifferentialFrames318.branch_structure ℚ c i

theorem infinity_structure :
    infinityEmbedding c ≫ ContactIntrinsicDifferentials318.structureMap c =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (IntegralInfinityChart318.Order ℚ c))) := by
  change (infinityChart ℚ c ≫ toOriginal c) ≫
    ((ContactProjectiveModel318.coverMap c).fromNormalization ≫ ProjectiveJLine318.structureMap ℚ) = _
  rw [Category.assoc,over_Q,infinityChart_structure]
end IntegralRationalFiveChartGeometry318
