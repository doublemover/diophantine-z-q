module
public import ProjectiveLineComplexChartGeometry318
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Topology.Compactification.OnePoint.Basic
public section
noncomputable section
namespace ProjectiveLineComplexSchemePoints318
open AlgebraicGeometry CategoryTheory Polynomial
open scoped OnePoint
set_option maxHeartbeats 1800000

/-- Actual base-preserving COMPLEX SCHEME-VALUED points of the fixed
homogeneous Proj projective line. Not points of a renamed sphere. -/
@[expose] def SchemePoints :=
  {f:Spec (CommRingCat.of ℂ) ⟶ ProjectiveJLine318.scheme ℂ //
    f ≫ ProjectiveJLine318.structureMap ℂ=Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))}
@[expose] def AffinePoints :=
  {f:Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)) //
    f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))}
@[expose] def affinePoint (z:ℂ) : AffinePoints :=
  Spec.homEquivAlgHom.symm (Polynomial.aeval z)
@[expose] def chartPoint (j:Fin 2) (z:ℂ) : SchemePoints :=
  ⟨(affinePoint z).val ≫ JLineAtlas318.chart ℂ j,by
    rw [Category.assoc,JLineAtlas318.chart_over_base]
    exact (affinePoint z).property⟩

lemma affinePoint_value (z:ℂ) : (affinePoint z).val=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval z).toRingHom) := rfl

lemma chartPoint_injective (j:Fin 2) : Function.Injective (chartPoint j) := by
  intro z w h
  have ha:affinePoint z=affinePoint w:=Subtype.ext
    ((cancel_mono (JLineAtlas318.chart ℂ j)).mp (congrArg Subtype.val h))
  have hh:=congrArg Spec.homEquivAlgHom ha
  have hh':Polynomial.aeval z=Polynomial.aeval w:=by
    simpa only [affinePoint,Equiv.apply_symm_apply] using hh
  simpa only [Polynomial.aeval_X] using congrArg
    (fun f:Polynomial ℂ→ₐ[ℂ]ℂ=>f Polynomial.X) hh'

lemma affinePoint_exhaustive (p:AffinePoints) : ∃z:ℂ,affinePoint z=p := by
  let φ:Polynomial ℂ→ₐ[ℂ]ℂ:=Spec.homEquivAlgHom p
  have he:φ=Polynomial.aeval (φ Polynomial.X):=by
    apply Polynomial.algHom_ext
    simp
  refine ⟨φ Polynomial.X,?_⟩
  unfold affinePoint
  rw [←he]
  exact Spec.homEquivAlgHom.symm_apply_apply p

/-- Exhaustion is by genuine morphisms over the original complex base. -/
theorem chartPoint_exhaustive (p:SchemePoints) : ∃j:Fin 2,∃z:ℂ,chartPoint j z=p := by
  obtain ⟨j,a,ha⟩:=ProjectiveLineComplexChartGeometry318.field_chart_cases p.val
  have hb:a ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)):=by
    rw [←JLineAtlas318.chart_over_base ℂ j,←Category.assoc,ha]
    exact p.property
  obtain ⟨z,hz⟩:=affinePoint_exhaustive ⟨a,hb⟩
  refine ⟨j,z,?_⟩
  apply Subtype.ext
  change (affinePoint z).val ≫ JLineAtlas318.chart ℂ j=p.val
  rw [hz]
  exact ha

/-- The ACTUAL standard charts identify reciprocal nonzero complex
coordinates, by equality of the original Scheme morphisms. -/
theorem reciprocal_overlap (z:ℂ) (hz:z≠0) : chartPoint 1 z=chartPoint 0 z⁻¹ := by
  apply Subtype.ext
  simpa only [chartPoint,affinePoint_value,Units.val_mk0,Units.val_inv_eq_inv_val] using
    (JLineOverlap318.unit_chart_overlap (R:=ℂ) (Units.mk0 z hz))

lemma chart_zero_preimage_one (z:ℂ) :
    (chartPoint 0 z).val ⁻¹ᵁ (JLineAtlas318.chart ℂ 1).opensRange=
      PrimeSpectrum.basicOpen z := by
  change ((affinePoint z).val ≫ JLineAtlas318.chart ℂ 0) ⁻¹ᵁ _=_
  rw [Scheme.Hom.comp_preimage,ProjectiveLineComplexChartGeometry318.chart_zero_preimage_one,
    affinePoint_value,SpecMap_preimage_basicOpen]
  simp

lemma infinity_ne_finite (z:ℂ) : chartPoint 0 0≠chartPoint 1 z := by
  intro he
  have hmem:(chartPoint 0 0).val default∈(JLineAtlas318.chart ℂ 1).opensRange:=by
    rw [he]
    exact ⟨(affinePoint z).val default,rfl⟩
  have hm:default∈(chartPoint 0 0).val ⁻¹ᵁ (JLineAtlas318.chart ℂ 1).opensRange:=hmem
  rw [chart_zero_preimage_one] at hm
  simpa using hm

/-- Full overlap equality of actual field-valued Scheme points. No
additional gluing identifications can occur beyond reciprocal coordinates. -/
theorem chartPoint_overlap_iff (z w:ℂ) :
    chartPoint 1 z=chartPoint 0 w ↔ z≠0 ∧ w=z⁻¹ := by
  constructor
  · intro he
    have hw:w≠0:=by
      intro hw
      subst w
      exact infinity_ne_finite z he.symm
    have hh:chartPoint 1 w⁻¹=chartPoint 0 w:=by
      simpa only [inv_inv] using reciprocal_overlap w⁻¹ (inv_ne_zero hw)
    have hz:w⁻¹=z:=chartPoint_injective 1 (hh.trans he.symm)
    refine ⟨hz ▸ inv_ne_zero hw,?_⟩
    rw [←hz,inv_inv]
  · rintro ⟨hz,rfl⟩
    exact reciprocal_overlap z hz

/-- The exact one-point parameterization includes the actual projective
infinity [1:0] and finite [z:1] Scheme morphisms. -/
@[expose] def spherePoint (p:OnePoint ℂ) : SchemePoints:=p.elim (chartPoint 0 0) (chartPoint 1)
lemma spherePoint_coe (z:ℂ) : spherePoint (z:OnePoint ℂ)=chartPoint 1 z:=rfl
lemma spherePoint_infty : spherePoint (∞:OnePoint ℂ)=chartPoint 0 0:=rfl

theorem spherePoint_bijective : Function.Bijective spherePoint := by
  constructor
  · intro p q he
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe z => exact False.elim (infinity_ne_finite z he)
    | coe z =>
      induction q using OnePoint.rec with
      | infty => exact False.elim (infinity_ne_finite z he.symm)
      | coe w => exact congrArg (fun x:ℂ=>(x:OnePoint ℂ)) (chartPoint_injective 1 he)
  · intro p
    obtain ⟨j,z,rfl⟩:=chartPoint_exhaustive p
    fin_cases j
    · by_cases hz:z=0
      · subst z
        exact ⟨∞,rfl⟩
      · refine ⟨(z⁻¹:ℂ),?_⟩
        exact (reciprocal_overlap z⁻¹ (inv_ne_zero hz)).trans (by rw [inv_inv])
    · exact ⟨(z:OnePoint ℂ),rfl⟩

@[expose] def sphereSchemeEquiv : OnePoint ℂ≃SchemePoints:=
  Equiv.ofBijective spherePoint spherePoint_bijective
end ProjectiveLineComplexSchemePoints318
