module
public import SelectedActualComplexGenericChartClosures318
public import NormalChart318
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedActualComplexGenericChartClosures318
namespace SelectedActualComplexGenericCompactNormal318

variable (K : Type) [Field K] [Algebra JField K]

instance generic_quasiCompact : QuasiCompact (genericMap K) := by
  letI : QuasiSeparatedSpace (ProjectiveJLine318.scheme ℂ) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveJLine318.structureMap ℂ)
  infer_instance

instance generic_quasiSeparated : QuasiSeparated (genericMap K) := by infer_instance

/-- One actual relative normalization, glued by the normalization of
the same whole generic field point over the original projective J-line. -/
abbrev model : Scheme := (genericMap K).normalization
abbrev modelMap : model K ⟶ ProjectiveJLine318.scheme ℂ :=
  (genericMap K).fromNormalization

@[expose] def targetCover (i : Fin 2) : (ProjectiveJLine318.scheme ℂ).affineOpens :=
  ⟨JLineAtlas318.chart ℂ i ''ᵁ ⊤,by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange _⟩

theorem targetCover_covers : (⨆ i, (targetCover i).1) = ⊤ := by
  simpa only [targetCover,Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range] using
    JLineAtlas318.standard_opens_cover ℂ

theorem model_integral : IsIntegral (model K) := by infer_instance

theorem generic_factorization :
    (genericMap K).toNormalization ≫ modelMap K = genericMap K :=
  (genericMap K).toNormalization_fromNormalization

variable [aK : Algebra ℂ K] [hTower : IsScalarTower ℂ JField K]
variable [hfin : FiniteDimensional JField K] [hsep : Algebra.IsSeparable JField K]

include aK hTower hfin hsep in
/-- Finiteness of the whole actual compact normalization follows by
the two proved trace-dual chart finitenesses on this same K. -/
theorem model_finite : IsFinite (modelMap K) := by
  apply GlobalNormalization318.finite_of_affine_pieces
    (genericMap K) targetCover targetCover_covers
  intro i
  change letI := ((genericMap K).app (JLineAtlas318.chart ℂ i ''ᵁ ⊤)).hom.toAlgebra
    Module.Finite Γ(ProjectiveJLine318.scheme ℂ,JLineAtlas318.chart ℂ i ''ᵁ ⊤)
      (integralClosure Γ(ProjectiveJLine318.scheme ℂ,JLineAtlas318.chart ℂ i ''ᵁ ⊤)
        Γ(Spec (CommRingCat.of K),(genericMap K)⁻¹ᵁ(JLineAtlas318.chart ℂ i ''ᵁ ⊤)))
  rw [genericMap_factor K i]
  exact NormalizationChart318.finite_sections
    (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℂ i) (closure_finite K i)

include aK hTower hfin hsep in
theorem model_proper :
    IsProper (modelMap K ≫ ProjectiveJLine318.structureMap ℂ) := by
  letI : IsFinite (modelMap K) := model_finite K
  infer_instance

/-- The actual ring of each affine chart of the very same global
normalization, not a separately constructed candidate compactification. -/
abbrev chartRing (i : Fin 2) : CommRingCat :=
  Γ(model K,(modelMap K)⁻¹ᵁ(targetCover i).1)

@[expose] def chartSectionsOfFactor {A B : CommRingCat} {Y : Scheme}
    (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (hf : f = Spec.map φ ≫ j) :
    letI := φ.hom.toAlgebra
    Γ(f.normalization,f.fromNormalization⁻¹ᵁ(j ''ᵁ ⊤)) ≃+* integralClosure A B := by
  subst f
  exact NormalChart318.sectionsEquiv φ j

include aK hTower in
@[expose] def chartRingEquiv (i : Fin 2) :
    letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
    chartRing K i ≃+* integralClosure ℂ[X] K := by
  letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
  change Γ((genericMap K).normalization,(genericMap K).fromNormalization⁻¹ᵁ
    (JLineAtlas318.chart ℂ i ''ᵁ ⊤)) ≃+* integralClosure ℂ[X] K
  exact chartSectionsOfFactor (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℂ i)
    (genericMap K) (genericMap_factor K i)

include aK hTower in
theorem chart_domain_normal (i : Fin 2) :
    IsDomain (chartRing K i) ∧ IsIntegrallyClosed (chartRing K i) := by
  letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
  letI : IsIntegrallyClosed (integralClosure ℂ[X] K) := closure_normal K i
  exact ⟨MulEquiv.isDomain _ (chartRingEquiv K i).toMulEquiv,
    IsIntegrallyClosed.of_equiv (chartRingEquiv K i).symm⟩

@[expose] def sourceCover (i : Fin 2) : (model K).affineOpens :=
  ⟨(modelMap K)⁻¹ᵁ(targetCover i).1,(targetCover i).2.preimage _⟩

theorem sourceCover_covers : (⨆ i, (sourceCover K i).1) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ targetCover_covers

private theorem chartSectionsOfFactor_genericReadout {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec F ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j)
    (htop : (⊤ : (Spec F).Opens) ≤ f.toNormalization ⁻¹ᵁ
      (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤))) :
    letI := φ.hom.toAlgebra
    CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (chartSectionsOfFactor φ j f hf).toRingHom) =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ⊤
        htop ≫ (Scheme.ΓSpecIso F).hom := by
  subst f
  let f := Spec.map φ ≫ j
  let U : Y.Opens := j ''ᵁ ⊤
  let V : f.normalization.Opens := f.fromNormalization ⁻¹ᵁ U
  letI := φ.hom.toAlgebra
  letI := (f.app U).hom.toAlgebra
  have hU : IsAffineOpen U := by
    change IsAffineOpen (j ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange j
  have hF : f ⁻¹ᵁ U = (⊤ : (Spec F).Opens) := NormalizationChart318.whole_preimage φ j
  have hV : f.toNormalization ⁻¹ᵁ V = (⊤ : (Spec F).Opens) := by
    change f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = ⊤
    rw [← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization, hF]
  have h₀ : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ V := by rw [hF,hV]
  have hEval : (f.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val
        (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom =
        f.toNormalization.appLE V (f ⁻¹ᵁ U) h₀ :=
    f.normalizationObjIso_hom_val hU
  have hb : CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (NormalChart318.sectionsEquiv φ j).toRingHom) =
      ((f.normalizationObjIso hU).hom ≫
        CommRingCat.ofHom (Subalgebra.val
          (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom) ≫
            (NormalizationChart318.sourceSections φ j).hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    unfold NormalChart318.sectionsEquiv
    rfl
  unfold chartSectionsOfFactor
  rw [hb,hEval]
  simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
    ← Category.assoc]
  rw [Scheme.Hom.appLE_map] <;> rfl

include aK hTower in
/-- A shallow equation for the published chart equivalence, exposing the
single named transported constructor without expanding its transport. -/
theorem chartRingEquiv_eq_chartSectionsOfFactor (i : Fin 2) :
    letI := (polynomial K i).toAlgebra
    chartRingEquiv K i =
      chartSectionsOfFactor (CommRingCat.ofHom (polynomial K i))
        (JLineAtlas318.chart ℂ i) (genericMap K) (genericMap_factor K i) := by
  rfl

include aK hTower in
/-- The same actual generic point belongs to each original compact chart. -/
theorem normalization_generic_top (i : Fin 2) :
    (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      (genericMap K).toNormalization ⁻¹ᵁ (sourceCover K i).1 := by
  change ⊤ ≤ (genericMap K).toNormalization ⁻¹ᵁ
    ((genericMap K).fromNormalization ⁻¹ᵁ (JLineAtlas318.chart ℂ i ''ᵁ ⊤))
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization, genericMap_factor K i]
  exact (NormalizationChart318.whole_preimage (CommRingCat.ofHom (polynomial K i))
    (JLineAtlas318.chart ℂ i)).ge

include aK hTower in
/-- On both literal charts, the existing published equivalence reads values by
the original generic morphism. The proof computes before specialization. -/
theorem chartRingEquiv_generic_readout (i : Fin 2) :
    let U := (sourceCover K i).1
    letI := (polynomial K i).toAlgebra
    CommRingCat.ofHom ((Subalgebra.val (integralClosure ℂ[X] K)).toRingHom.comp
      (chartRingEquiv K i).toRingHom) =
      (genericMap K).toNormalization.appLE U ⊤ (normalization_generic_top K i) ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
  letI := (polynomial K i).toAlgebra
  have hβ := congrArg
    (fun s : chartRing K i ≃+* integralClosure ℂ[X] K =>
      CommRingCat.ofHom ((Subalgebra.val (integralClosure ℂ[X] K)).toRingHom.comp s.toRingHom))
    (chartRingEquiv_eq_chartSectionsOfFactor K i)
  exact hβ.trans (chartSectionsOfFactor_genericReadout
    (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℂ i)
    (genericMap K) (genericMap_factor K i) (normalization_generic_top K i))

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

end SelectedActualComplexGenericCompactNormal318

#print axioms SelectedActualComplexGenericCompactNormal318.model_finite
#print axioms SelectedActualComplexGenericCompactNormal318.chartRingEquiv
#print axioms SelectedActualComplexGenericCompactNormal318.normal_stalk

#print axioms SelectedActualComplexGenericCompactNormal318.chartRingEquiv_eq_chartSectionsOfFactor
#print axioms SelectedActualComplexGenericCompactNormal318.chartRingEquiv_generic_readout
