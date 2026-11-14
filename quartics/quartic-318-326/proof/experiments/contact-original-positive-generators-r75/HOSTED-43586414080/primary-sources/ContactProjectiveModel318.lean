module
public import ContactKummerOpenDomain318
public import JLineOverlap318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace ContactProjectiveModel318
open CategoryTheory AlgebraicGeometry
open ContactKummerOrder318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The actual four-contact base open in the projective contact line.
This reuses the projective-line scheme, not the modular meaning of its coordinate. -/
@[expose] def baseOpen : ContactKummerCover318.base⟶ProjectiveJLine318.scheme ℚ :=
  ContactKummerCover318.baseMap≫JLineAtlas318.chart ℚ 1
instance baseOpen_open : IsOpenImmersion baseOpen := by
  letI:=ContactKummerCover318.base_open
  unfold baseOpen
  infer_instance

theorem baseOpen_over_Q : baseOpen≫ProjectiveJLine318.structureMap ℚ=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ OpenBase)) := by
  rw [baseOpen,Category.assoc,JLineAtlas318.chart_over_base]
  unfold ContactKummerCover318.baseMap
  rw [←Spec.map_comp]
  congr 1

theorem base_t_unit : IsUnit (algebraMap R OpenBase Polynomial.X) := by
  apply IsLocalization.Away.isUnit_of_dvd denominator
  have h:=Finset.dvd_prod_of_mem (fun i:Fin 4=>Polynomial.X-Polynomial.C
    (LinearContactSquareclass318.contacts i)) (Finset.mem_univ (0:Fin 4))
  simpa [denominator,LinearContactSquareclass318.contacts] using h

theorem baseOpen_at_infinity : baseOpen=
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (↑(base_t_unit.unit)⁻¹:OpenBase)).toRingHom)≫JLineAtlas318.chart ℚ 0 := by
  have he:(Polynomial.aeval (↑base_t_unit.unit:OpenBase)).toRingHom=
      algebraMap R OpenBase := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply ℚ R OpenBase q
    · simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X] using base_t_unit.unit_spec
  have e:=JLineOverlap318.unit_chart_overlap (R:=ℚ) base_t_unit.unit
  rw [he] at e
  exact e

@[expose] def coverMap (c:Fin 4→ℚˣ) : ContactKummerCover318.cover c⟶ProjectiveJLine318.scheme ℚ :=
  ContactKummerCover318.structureMap c≫baseOpen

theorem coverMap_at_infinity (c:Fin 4→ℚˣ) : coverMap c=
    ContactKummerCover318.structureMap c≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (↑(base_t_unit.unit)⁻¹:OpenBase)).toRingHom)≫JLineAtlas318.chart ℚ 0 := by
  rw [coverMap,baseOpen_at_infinity]

theorem coverMap_properties (c:Fin 4→ℚˣ) :
    LocallyOfFiniteType (coverMap c) ∧ LocallyQuasiFinite (coverMap c) ∧
    IsSeparated (coverMap c) ∧ QuasiCompact (coverMap c) := by
  letI:IsFinite (ContactKummerCover318.structureMap c):=(ContactKummerCover318.finite_etale c).1
  unfold coverMap baseOpen ContactKummerCover318.baseMap
  exact ⟨inferInstance,inferInstance,inferInstance,inferInstance⟩
instance coverMap_quasiCompact (c:Fin 4→ℚˣ) : QuasiCompact (coverMap c):=
  (coverMap_properties c).2.2.2
instance coverMap_separated (c:Fin 4→ℚˣ) : IsSeparated (coverMap c):=
  (coverMap_properties c).2.2.1

/-- A genuine globally glued relative normalization over the projective
contact line, constructed from the actual source open cover. -/
abbrev model (c:Fin 4→ℚˣ) : Scheme:=(coverMap c).normalization
@[expose] def sourceOpen (c:Fin 4→ℚˣ) : ContactKummerCover318.cover c⟶model c:=
  (coverMap c).toNormalization
@[expose] def modelMap (c:Fin 4→ℚˣ) : model c⟶ProjectiveJLine318.scheme ℚ:=
  (coverMap c).fromNormalization

theorem sourceOpen_open (c:Fin 4→ℚˣ) : IsOpenImmersion (sourceOpen c) := by
  letI:LocallyOfFiniteType (coverMap c):=(coverMap_properties c).1
  letI:LocallyQuasiFinite (coverMap c):=(coverMap_properties c).2.1
  exact inferInstanceAs (IsOpenImmersion (coverMap c).toNormalization)
theorem sourceOpen_dense (c:Fin 4→ℚˣ) : IsDominant (sourceOpen c) := by
  change IsDominant (coverMap c).toNormalization
  infer_instance
theorem modelMap_integral (c:Fin 4→ℚˣ) : IsIntegralHom (modelMap c) := by
  change IsIntegralHom (coverMap c).fromNormalization
  infer_instance
theorem factorization (c:Fin 4→ℚˣ) : sourceOpen c≫modelMap c=coverMap c :=
  (coverMap c).toNormalization_fromNormalization

theorem model_integral (c:Fin 4→ℚˣ) : IsIntegral (model c) := by
  letI:IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
  letI:IsIntegral (ContactKummerCover318.cover c):=inferInstanceAs
    (IsIntegral (Spec (CommRingCat.of (OpenOrder c))))
  infer_instance
end ContactProjectiveModel318
