module
public import RationalContactPoint318
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace ContactFieldSection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (t : ℚ)
abbrev L := RationalContactPoint318.PointField c t
abbrev Base := Spec (CommRingCat.of ℚ)
abbrev FieldBase := Spec (CommRingCat.of (L c t))

/-- The original rational structure map, with no replacement of the model. -/
@[expose] def sourceStructure : ContactProjectiveModel318.model c ⟶ Base :=
  ContactProjectiveModel318.modelMap c ≫ ProjectiveJLine318.structureMap ℚ

@[expose] def fieldMap : FieldBase c t ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (L c t)))

lemma point_over_base : RationalContactPoint318.point c t ≫ sourceStructure c = fieldMap c t := by
  rw [sourceStructure, ← Category.assoc, RationalContactPoint318.point_over_coordinate,
    Category.assoc, JLineAtlas318.chart_over_base, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext q
  simp [fieldMap, RingHom.comp_apply]

instance fieldMap_finite : IsFinite (fieldMap c t) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

instance fieldMap_etale : Etale (fieldMap c t) := by
  let _ : Algebra.FormallyEtale ℚ (L c t) := Algebra.FormallyEtale.of_isSeparable ℚ (L c t)
  let _ : Algebra.Etale ℚ (L c t) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

lemma fieldMap_flat_surjective : Flat (fieldMap c t) ∧ Surjective (fieldMap c t) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  have hf : Module.FaithfullyFlat ℚ (L c t) := inferInstance
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr hf

instance fieldMap_surjective : Surjective (fieldMap c t) := (fieldMap_flat_surjective c t).2

/-- This explicit degree-at-most-sixteen field extension is an actual fppf
cover of the original rational base. -/
theorem fppf_cover : Presieve.singleton (fieldMap c t) ∈ Scheme.fppfPrecoverage Base :=
  (fieldMap c t).singleton_mem_fppfPrecoverage

theorem fppf_sieve : Sieve.generate (Presieve.singleton (fieldMap c t)) ∈
    Scheme.fppfTopology Base :=
  Precoverage.generate_mem_toGrothendieck (fppf_cover c t)

/-- The actual chosen field-valued point becomes a section of the original
source after the actual scheme-theoretic base change. No rational section
of the source over Q is asserted. -/
@[expose] def pointSection : FieldBase c t ⟶ pullback (sourceStructure c) (fieldMap c t) :=
  pullback.lift (RationalContactPoint318.point c t) (𝟙 _) (by
    simpa using point_over_base c t)

@[reassoc] theorem pointSection_fst :
    pointSection c t ≫ pullback.fst (sourceStructure c) (fieldMap c t) =
      RationalContactPoint318.point c t := pullback.lift_fst _ _ _

@[reassoc] theorem pointSection_snd :
    pointSection c t ≫ pullback.snd (sourceStructure c) (fieldMap c t) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end ContactFieldSection318
