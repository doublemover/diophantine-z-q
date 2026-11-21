module
public import SelectedOriginalGenericChartClosures318
public import NormalChart318
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalGenericChartClosures318
namespace SelectedOriginalGenericCompactNormal318

variable (K : Type) [Field K] [Algebra JField K]

instance generic_quasiCompact : QuasiCompact (genericMap K) := by
  letI : QuasiSeparatedSpace (ProjectiveJLine318.scheme ℚ) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveJLine318.structureMap ℚ)
  infer_instance

instance generic_quasiSeparated : QuasiSeparated (genericMap K) := by infer_instance

/-- One actual relative normalization, glued by the normalization of
the same whole generic field point over the original projective J-line. -/
abbrev model : Scheme := (genericMap K).normalization
abbrev modelMap : model K ⟶ ProjectiveJLine318.scheme ℚ :=
  (genericMap K).fromNormalization

@[expose] def targetCover (i : Fin 2) : (ProjectiveJLine318.scheme ℚ).affineOpens :=
  ⟨JLineAtlas318.chart ℚ i ''ᵁ ⊤,by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange _⟩

theorem targetCover_covers : (⨆ i, (targetCover i).1) = ⊤ := by
  simpa only [targetCover,Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range] using
    JLineAtlas318.standard_opens_cover ℚ

theorem model_integral : IsIntegral (model K) := by infer_instance

theorem generic_factorization :
    (genericMap K).toNormalization ≫ modelMap K = genericMap K :=
  (genericMap K).toNormalization_fromNormalization

variable [aK : Algebra ℚ K] [hTower : IsScalarTower ℚ JField K]
variable [hfin : FiniteDimensional JField K] [hsep : Algebra.IsSeparable JField K]

include aK hTower hfin hsep in
/-- Finiteness of the whole actual compact normalization follows by
the two proved trace-dual chart finitenesses on this same K. -/
theorem model_finite : IsFinite (modelMap K) := by
  apply GlobalNormalization318.finite_of_affine_pieces
    (genericMap K) targetCover targetCover_covers
  intro i
  change letI := ((genericMap K).app (JLineAtlas318.chart ℚ i ''ᵁ ⊤)).hom.toAlgebra
    Module.Finite Γ(ProjectiveJLine318.scheme ℚ,JLineAtlas318.chart ℚ i ''ᵁ ⊤)
      (integralClosure Γ(ProjectiveJLine318.scheme ℚ,JLineAtlas318.chart ℚ i ''ᵁ ⊤)
        Γ(Spec (CommRingCat.of K),(genericMap K)⁻¹ᵁ(JLineAtlas318.chart ℚ i ''ᵁ ⊤)))
  rw [genericMap_factor K i]
  exact NormalizationChart318.finite_sections
    (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℚ i) (closure_finite K i)

include aK hTower hfin hsep in
theorem model_proper :
    IsProper (modelMap K ≫ ProjectiveJLine318.structureMap ℚ) := by
  letI : IsFinite (modelMap K) := model_finite K
  infer_instance

/-- The actual ring of each affine chart of the very same global
normalization, not a separately constructed candidate compactification. -/
abbrev chartRing (i : Fin 2) : CommRingCat :=
  Γ(model K,(modelMap K)⁻¹ᵁ(targetCover i).1)

include aK hTower in
@[expose] def chartRingEquiv (i : Fin 2) :
    letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
    chartRing K i ≃+* integralClosure ℚ[X] K := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  change Γ((genericMap K).normalization,(genericMap K).fromNormalization⁻¹ᵁ
    (JLineAtlas318.chart ℚ i ''ᵁ ⊤)) ≃+* integralClosure ℚ[X] K
  let chartSections {A B : CommRingCat} {Y : Scheme}
      (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
      (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (hf : f = Spec.map φ ≫ j) :
      letI := φ.hom.toAlgebra
      Γ(f.normalization,f.fromNormalization⁻¹ᵁ(j ''ᵁ ⊤)) ≃+* integralClosure A B := by
    subst f
    exact NormalChart318.sectionsEquiv φ j
  exact chartSections (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℚ i)
    (genericMap K) (genericMap_factor K i)

include aK hTower in
theorem chart_domain_normal (i : Fin 2) :
    IsDomain (chartRing K i) ∧ IsIntegrallyClosed (chartRing K i) := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : IsIntegrallyClosed (integralClosure ℚ[X] K) := closure_normal K i
  exact ⟨MulEquiv.isDomain _ (chartRingEquiv K i).toMulEquiv,
    IsIntegrallyClosed.of_equiv (chartRingEquiv K i).symm⟩

@[expose] def sourceCover (i : Fin 2) : (model K).affineOpens :=
  ⟨(modelMap K)⁻¹ᵁ(targetCover i).1,(targetCover i).2.preimage _⟩

theorem sourceCover_covers : (⨆ i, (sourceCover K i).1) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ targetCover_covers

include aK hTower in
/-- Normality at every actual stalk, not just in the abstract model
rings, by the genuine two-chart cover and localization at its prime. -/
theorem normal_stalk (x : model K) :
    IsIntegrallyClosed ((model K).presheaf.stalk x) := by
  have hx : x ∈ (⨆ i, (sourceCover K i).1) := by
    rw [sourceCover_covers]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := sourceCover K i
  letI : IsDomain Γ(model K,U) := (chart_domain_normal K i).1
  letI : IsIntegrallyClosed Γ(model K,U) := (chart_domain_normal K i).2
  letI := (model K).presheaf.algebra_section_stalk ⟨x,hi⟩
  letI := U.2.isLocalization_stalk ⟨x,hi⟩
  exact isIntegrallyClosed_of_isLocalization _ (U.2.primeIdealOf ⟨x,hi⟩).asIdeal.primeCompl
    (U.2.primeIdealOf ⟨x,hi⟩).asIdeal.primeCompl_le_nonZeroDivisors

end SelectedOriginalGenericCompactNormal318

#print axioms SelectedOriginalGenericCompactNormal318.model_finite
#print axioms SelectedOriginalGenericCompactNormal318.chartRingEquiv
#print axioms SelectedOriginalGenericCompactNormal318.normal_stalk
