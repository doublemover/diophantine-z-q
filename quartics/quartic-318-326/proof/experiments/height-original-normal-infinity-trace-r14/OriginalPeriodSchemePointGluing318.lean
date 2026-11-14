module
public import OriginalPeriodSchemeChartPoints318
public section
noncomputable section
namespace OriginalPeriodSchemePointGluing318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OriginalPeriodWeierstrassCoordinates318 OriginalPeriodProjectiveModel318
open OriginalPeriodNativeChartGerms318 OriginalPeriodSchemeChartPoints318
open ComplexAffineFreeTranslation318 WeierstrassOverlap318 Filter Topology
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
variable (q : Torus L)
variable (hq : nativeV L q-nativeU L q^3-A L*nativeU L q*nativeV L q^2-B L*nativeV L q^3=0)

@[expose] def infinityPoint : Spec (CommRingCat.of ℂ) ⟶ model L :=
  Spec.map (CommRingCat.ofHom (infinityEvaluation L q hq).toRingHom) ≫
    WeierstrassGluing318.infinityChart (A L) (B L)

variable (hv : nativeV L q≠0)
@[expose] def overlapEvaluation : InfinityOverlap (A L) (B L) →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom
    (R := InfinityChart318.Ring (A L) (B L))
    (S := InfinityOverlap (A L) (B L)) (P := ℂ)
    (f := infinityEvaluation L q hq) (InfinityChart318.z (A L) (B L))
    (by rw [infinity_z,isUnit_iff_ne_zero]; exact hv)
lemma overlap_map (a : InfinityChart318.Ring (A L) (B L)) :
    overlapEvaluation L q hq hv (algebraMap _ (InfinityOverlap (A L) (B L)) a)=
      infinityEvaluation L q hq a := by
  simp only [overlapEvaluation,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
lemma overlap_x : overlapEvaluation L q hq hv (ix (A L) (B L))=nativeU L q := by
  rw [ix,overlap_map,infinity_x]
lemma overlap_z : overlapEvaluation L q hq hv (iz (A L) (B L))=nativeV L q := by
  rw [iz,overlap_map,infinity_z]
lemma overlap_inverse : overlapEvaluation L q hq hv (ii (A L) (B L))=1/nativeV L q := by
  have h := congrArg (overlapEvaluation L q hq hv) (iz_ii (A L) (B L))
  rw [map_mul,map_one,overlap_z] at h
  apply (eq_div_iff hv).mpr
  simpa only [mul_comm] using h

/-- Equality of the ENTIRE finite coordinate-ring evaluation, not just a
point bijection: actual localization maps recover both original coordinates. -/
theorem finite_evaluation_square (hn : q≠0) (hy : y L q/2≠0)
    (hu : nativeU L q=x L q/(y L q/2)) (hz : nativeV L q=1/(y L q/2)) :
    (overlapEvaluation L q hq hv).comp (toInfinityBase (A L) (B L))=finiteEvaluation L ⟨q,hn⟩ := by
  apply affine_hom_ext
  · rw [AlgHom.comp_apply,toInfinityBase_x,map_mul,overlap_x,overlap_inverse,finite_x,hu,hz]
    field_simp [hy]
  · rw [AlgHom.comp_apply,toInfinityBase_y,overlap_inverse,finite_y,hz]
    field_simp [hy]

/-- The original finite and infinity scheme-valued points are equal
through the ACTUAL localization gluing of the independently defined scheme. -/
theorem scheme_points_agree (hn : q≠0) (hy : y L q/2≠0)
    (hu : nativeU L q=x L q/(y L q/2)) (hz : nativeV L q=1/(y L q/2)) :
    finitePoint L ⟨q,hn⟩=infinityPoint L q hq := by
  let s := Spec.map (CommRingCat.ofHom (overlapEvaluation L q hq hv).toRingHom)
  have hfinite : s ≫ WeierstrassGluing318.intoAffine (A L) (B L)=
      Spec.map (CommRingCat.ofHom (finiteEvaluation L ⟨q,hn⟩).toRingHom) := by
    rw [WeierstrassGluing318.intoAffine_eq]
    dsimp [s]
    rw [←Spec.map_comp]
    have he := finite_evaluation_square L q hq hv hn hy hu hz
    exact congrArg (fun f : ShortAffineJacobian318.Ring (A L) (B L) →ₐ[ℂ] ℂ =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) he
  have hinfinity : s ≫ WeierstrassGluing318.intoInfinity (A L) (B L)=
      Spec.map (CommRingCat.ofHom (infinityEvaluation L q hq).toRingHom) := by
    dsimp [s,WeierstrassGluing318.intoInfinity]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact overlap_map L q hq hv
  unfold finitePoint infinityPoint
  rw [←hfinite,←hinfinity,Category.assoc,Category.assoc]
  congr 1
  exact pushout.condition

/-- The comparison holds on a genuine original neighborhood, with all
localization nonzero premises constructed from the original overlap theorem. -/
theorem original_neighborhood_gluing : ∀ᶠ q in 𝓝 (0:Torus L),
    ∀hn:q≠0,∃hq:nativeV L q-nativeU L q^3-A L*nativeU L q*nativeV L q^2-B L*nativeV L q^3=0,
      finitePoint L ⟨q,hn⟩=infinityPoint L q hq := by
  filter_upwards [infinity_equation L,overlap L] with q hq ho
  intro hn
  obtain ⟨hy,hu,hz⟩ := ho hn
  have hv : nativeV L q≠0 := by rw [hz]; exact div_ne_zero one_ne_zero hy
  exact ⟨hq,scheme_points_agree L q hq hv hn hy hu hz⟩
end OriginalPeriodSchemePointGluing318
