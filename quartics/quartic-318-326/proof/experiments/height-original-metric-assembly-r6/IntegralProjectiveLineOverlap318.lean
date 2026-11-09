module
public import IntegralOriginalFiniteFlatPencil318
public import ClutchedModuleFrames318
public section
noncomputable section
namespace IntegralProjectiveLineOverlap318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]
abbrev A := Localization.Away (X:R[X])
@[expose] def t : A R := algebraMap R[X] (A R) X
@[expose] def tUnit : (A R)ˣ := (IsLocalization.Away.algebraMap_isUnit (X:R[X]) (S:=A R)).unit
theorem tUnit_coe : (tUnit R:A R)=t R := IsUnit.unit_spec _
@[expose] def s : A R := ↑(tUnit R)⁻¹
@[expose] def finiteInclusion : Spec (CommRingCat.of (A R)) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap R[X] (A R)))
@[expose] def infinityInclusion : Spec (CommRingCat.of (A R)) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) (s R)).toRingHom)
instance finite_open : IsOpenImmersion (finiteInclusion R) := by
  unfold finiteInclusion A
  infer_instance

theorem maps_agree : finiteInclusion R ≫ JLineAtlas318.chart R 1=
    infinityInclusion R ≫ JLineAtlas318.chart R 0 := by
  have he : (Polynomial.aeval (R:=R) (tUnit R:A R)).toRingHom=algebraMap R[X] (A R) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,Polynomial.algebraMap_eq] using
        IsScalarTower.algebraMap_apply R R[X] (A R) r
    · simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,t] using tUnit_coe R
  simpa only [he,finiteInclusion,infinityInclusion,s] using
    JLineOverlap318.unit_chart_overlap (R:=R) (tUnit R)
@[expose] def embedding : Spec (CommRingCat.of (A R)) ⟶ ProjectiveJLine318.scheme R :=
  finiteInclusion R ≫ JLineAtlas318.chart R 1
instance embedding_open : IsOpenImmersion (embedding R) := by unfold embedding;infer_instance
instance infinity_open : IsOpenImmersion (infinityInclusion R) := by
  haveI : IsOpenImmersion (infinityInclusion R ≫ JLineAtlas318.chart R 0) := by
    rw [←maps_agree]
    infer_instance
  exact IsOpenImmersion.of_comp _ (JLineAtlas318.chart R 0)

theorem finite_range : (finiteInclusion R).opensRange=PrimeSpectrum.basicOpen (X:R[X]) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (A R) (X:R[X])
theorem finite_intersection :
    JLineAtlas318.chart R 1 ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=(finiteInclusion R).opensRange := by
  rw [←Scheme.Hom.image_top_eq_opensRange,
    IntegralProjectiveChartIntersection318.chart_one_preimage_zero,finite_range]
theorem full_intersection : (JLineAtlas318.chart R 1).opensRange ⊓
    (JLineAtlas318.chart R 0).opensRange=(embedding R).opensRange := by
  rw [←Scheme.Hom.image_preimage_eq_opensRange_inf,finite_intersection,←Scheme.Hom.opensRange_comp]
  rfl
theorem infinity_intersection :
    JLineAtlas318.chart R 0 ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=(infinityInclusion R).opensRange := by
  have h := congrArg (fun U => JLineAtlas318.chart R 0 ⁻¹ᵁ U) (full_intersection R)
  rw [Scheme.Hom.preimage_inf,Scheme.Hom.preimage_opensRange,inf_top_eq] at h
  simp only [embedding,maps_agree,Scheme.Hom.opensRange_comp,Scheme.Hom.preimage_image_eq] at h
  exact h

theorem ts : t R*s R=1 := by
  simpa only [←tUnit_coe,s] using Units.mul_inv (tUnit R)
end IntegralProjectiveLineOverlap318
