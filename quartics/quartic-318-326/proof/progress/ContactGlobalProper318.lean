module
public import ContactReciprocalCover318
public import NormalizationChart318
public section
noncomputable section
namespace ContactGlobalProper318
open CategoryTheory AlgebraicGeometry
open ContactKummerOrder318
set_option maxHeartbeats 0
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def targetCover (j:Fin 2) : (ProjectiveJLine318.scheme ℚ).affineOpens :=
  ⟨JLineAtlas318.chart ℚ j ''ᵁ ⊤,by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange _⟩
theorem targetCover_covers : (⨆j,(targetCover j).1)=⊤ := by
  simpa only [targetCover,Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range] using
    JLineAtlas318.standard_opens_cover ℚ

variable (c:Fin 4→ℚˣ)
local instance sourceDomain : IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance sourceFinite : Module.Finite OpenBase (OpenOrder c):=(open_finite_free_etale c).1
local instance sourceEtale : Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2

@[expose] def finitePolynomial : R→+*OpenOrder c :=
  (algebraMap OpenBase (OpenOrder c)).comp (algebraMap R OpenBase)

theorem finite_factor : ContactProjectiveModel318.coverMap c=
    Spec.map (CommRingCat.ofHom (finitePolynomial c))≫JLineAtlas318.chart ℚ 1 := by
  unfold ContactProjectiveModel318.coverMap ContactProjectiveModel318.baseOpen
    ContactKummerCover318.structureMap ContactKummerCover318.baseMap finitePolynomial
  rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

theorem reciprocal_factor : ContactProjectiveModel318.coverMap c=
    Spec.map (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap (OpenOrder c)))≫
      JLineAtlas318.chart ℚ 0 := by
  have he:ContactReciprocalCover318.polynomialMap (OpenOrder c)=
      (algebraMap OpenBase (OpenOrder c)).comp
        (Polynomial.aeval (↑(ContactProjectiveModel318.base_t_unit.unit)⁻¹:OpenBase)).toRingHom := by
    apply RingHom.ext
    intro p
    change algebraMap OpenBase (OpenOrder c)
      (ContactReciprocalBase318.backward (algebraMap R ContactReciprocalBase318.Base p))=_
    rw [ContactReciprocalBase318.backward_map]
    rfl
  rw [he,CommRingCat.ofHom_comp,Spec.map_comp]
  exact ContactProjectiveModel318.coverMap_at_infinity c

theorem finite_chart_closure :
    letI:=(finitePolynomial c).toAlgebra
    Module.Finite R (integralClosure R (OpenOrder c)) :=
  (ContactReciprocalCover318.original_finite_normal_model (OpenOrder c)).1

theorem finite_sections_of_factor {A B:CommRingCat} {Y:Scheme}
    (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j] (f:Spec B⟶Y)
    (he:f=Spec.map φ≫j)
    (hf:letI:=φ.hom.toAlgebra;Module.Finite A (integralClosure A B)) :
    letI:=(f.app (j ''ᵁ ⊤)).hom.toAlgebra
    Module.Finite Γ(Y,j ''ᵁ ⊤)
      (integralClosure Γ(Y,j ''ᵁ ⊤) Γ(Spec B,f⁻¹ᵁ(j ''ᵁ ⊤))) := by
  subst f
  exact NormalizationChart318.finite_sections φ j hf

/-- Both actual affine normalization interfaces are discharged using the
literal t and 1/t maps on the same entire original source cover. -/
theorem normalization_finite : IsFinite (ContactProjectiveModel318.modelMap c) := by
  apply GlobalNormalization318.finite_of_affine_pieces
    (ContactProjectiveModel318.coverMap c) targetCover targetCover_covers
  intro i
  fin_cases i
  · dsimp only [targetCover,ContactKummerCover318.cover]
    exact finite_sections_of_factor
      (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap (OpenOrder c)))
      (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.coverMap c) (reciprocal_factor c)
      (by exact (ContactReciprocalCover318.finite_normal_model (OpenOrder c)).1)
  · dsimp only [targetCover,ContactKummerCover318.cover]
    exact finite_sections_of_factor
      (CommRingCat.ofHom (finitePolynomial c)) (JLineAtlas318.chart ℚ 1)
      (ContactProjectiveModel318.coverMap c) (finite_factor c) (finite_chart_closure c)

/-- A genuine proper integral model over Q, containing the original
contact cover as an actual dense open. No properness assumption is supplied. -/
theorem proper_integral_extension :
    IsOpenImmersion (ContactProjectiveModel318.sourceOpen c) ∧
    IsIntegral (ContactProjectiveModel318.model c) ∧
    IsProper (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ) := by
  letI:=normalization_finite c
  exact ⟨ContactProjectiveModel318.sourceOpen_open c,
    ContactProjectiveModel318.model_integral c,inferInstance⟩
end ContactGlobalProper318
