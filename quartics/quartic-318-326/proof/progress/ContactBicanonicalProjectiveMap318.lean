module
public import ContactBicanonicalSectionRatios318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace ContactBicanonicalProjectiveMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The finite chart morphism is constructed by evaluating the polynomial
coordinate at the uniquely characterized section ratio q1/q0. -/
@[expose] def branchMap (i : Fin 4) :
    ContactIntrinsicFrames318.chart c (some i) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval
    (ContactBicanonicalRatios318.branchRatio c i)).toRingHom) ≫ JLineAtlas318.chart ℚ 1

/-- At infinity evaluate the opposite projective coordinate at q0/q1. -/
@[expose] def infinityMap :
    ContactIntrinsicFrames318.chart c none ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval
    (ContactBicanonicalRatios318.infinityRatio c)).toRingHom) ≫ JLineAtlas318.chart ℚ 0

theorem branch_polynomial (i : Fin 4) :
    (Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom=
      (algebraMap (ContactKummerOrder318.SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i)).comp
        (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c)) := by
  apply Polynomial.ringHom_ext
  · intro q
    simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,RingHom.comp_apply]
    exact (RingHom.map_rat_algebraMap _ q).symm.trans (RingHom.map_rat_algebraMap _ q).symm
  · simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,RingHom.comp_apply,
      ContactBicanonicalRatios318.branchRatio_eq]
    rfl

theorem infinity_polynomial :
    (Polynomial.aeval (ContactBicanonicalRatios318.infinityRatio c)).toRingHom=
      (ReciprocalInfinityBase318.chartMap c).comp
        (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen c)) := by
  apply Polynomial.ringHom_ext
  · intro q
    simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,RingHom.comp_apply]
    exact (RingHom.map_rat_algebraMap _ q).symm.trans (RingHom.map_rat_algebraMap _ q).symm
  · simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,RingHom.comp_apply]
    exact (ContactBicanonicalRatios318.infinityRatio_eq c).trans
      (ContactBicanonicalRatios318.reciprocalCoordinate_base c).symm

/-- Exact comparison with the existing contact-line structural morphism. -/
theorem branch_comparison (i : Fin 4) :
    ContactIntrinsicFrames318.branchEmbedding c i ≫ ContactProjectiveModel318.modelMap c = branchMap c i := by
  unfold ContactIntrinsicFrames318.branchEmbedding ContactProjectiveModel318.modelMap
  rw [Category.assoc,SourceGlobalAffine318.chartEmbedding_over_contact_line]
  unfold branchMap
  rw [branch_polynomial,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

theorem infinity_comparison :
    InfinityGlobalScheme318.chartEmbedding c ≫ ContactProjectiveModel318.modelMap c = infinityMap c := by
  change InfinityGlobalScheme318.chartEmbedding c ≫
    (ContactProjectiveModel318.coverMap c).fromNormalization = _
  rw [InfinityStructureMap318.chartEmbedding_over_contact_line]
  unfold infinityMap InfinityGlobalBase318.baseOpen ReciprocalInfinityNormalization318.structureMap
  rw [infinity_polynomial,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

@[expose] def localMap : (i : Option (Fin 4)) →
    (ContactIntrinsicFrames318.cover c).X i ⟶ ProjectiveJLine318.scheme ℚ
  | some i => branchMap c i
  | none => infinityMap c

theorem local_comparison (i : Option (Fin 4)) :
    (ContactIntrinsicFrames318.cover c).f i ≫ ContactProjectiveModel318.modelMap c=localMap c i := by
  cases i
  · exact infinity_comparison c
  · exact branch_comparison c _

/-- Compatibility is equality on actual categorical intersections. -/
theorem local_compatible (i j : Option (Fin 4)) :
    pullback.fst ((ContactIntrinsicFrames318.cover c).f i) ((ContactIntrinsicFrames318.cover c).f j) ≫
      localMap c i = pullback.snd _ _ ≫ localMap c j := by
  rw [←local_comparison,←local_comparison,←Category.assoc,←Category.assoc,pullback.condition]

/-- The actual Scheme morphism obtained by gluing the local ratios of the
actual global pair. Coordinate convention is [q1:q0], with t=q1/q0. -/
@[expose] def projectiveMap : ContactGlobalSmooth318.Model c ⟶ ProjectiveJLine318.scheme ℚ :=
  (ContactIntrinsicFrames318.cover c).glueMorphisms (localMap c) (local_compatible c)

theorem projectiveMap_local (i : Option (Fin 4)) :
    (ContactIntrinsicFrames318.cover c).f i ≫ projectiveMap c=localMap c i :=
  (ContactIntrinsicFrames318.cover c).ι_glueMorphisms _ _ i

/-- The section-constructed projective morphism is exactly the original
normalization morphism, not merely equal on rational or geometric points. -/
theorem projectiveMap_eq : projectiveMap c=ContactProjectiveModel318.modelMap c := by
  apply (ContactIntrinsicFrames318.cover c).hom_ext
  intro i
  exact (projectiveMap_local c i).trans (local_comparison c i).symm

theorem projectiveMap_finite : IsFinite (projectiveMap c) := by
  rw [projectiveMap_eq]
  exact ContactGlobalProper318.normalization_finite c

theorem projectiveMap_proper : IsProper (projectiveMap c) := by
  letI := projectiveMap_finite c
  infer_instance
end ContactBicanonicalProjectiveMap318
