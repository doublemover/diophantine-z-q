module
public import ContactUniversalGlobalFunctions318
public import UniversalSectionEvaluation318
public import RigidifiedRelativeClass318
public import ContactFieldSection318
public section
noncomputable section
namespace ContactUniversalRigidifiedClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SourceTwistArithmetic318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (t : ℚ)
abbrev FieldBase := ContactFieldSection318.FieldBase units t
abbrev fieldMap := ContactFieldSection318.fieldMap units t
abbrev Family := pullback ContactUniversalGlobalFunctions318.p (fieldMap t)
abbrev q : Family t ⟶ FieldBase t := pullback.snd _ _
abbrev e : FieldBase t ⟶ Family t := ContactFieldSection318.pointSection units t
lemma section_eq : e t ≫ q t = 𝟙 _ := ContactFieldSection318.pointSection_snd units t

instance family_proper : IsProper (q t) := inferInstance
instance family_appTop_isIso : IsIso (q t).appTop :=
  ContactUniversalGlobalFunctions318.app_isIso (fieldMap t) ⊤

/-- The original section after arbitrary further scheme base change. -/
abbrev testSection {T : Scheme} (b : T ⟶ FieldBase t) :=
  RelativeSectionBaseChange318.sectionOn (q t) (e t) (section_eq t) b

/-- Actual section evaluation is bijective for every test scheme, with
no field, reducedness, affine, or quasicompact hypothesis on that test. -/
lemma test_evaluation_bijective {T : Scheme} (b : T ⟶ FieldBase t) :
    Function.Bijective (testSection t b).appTop :=
  UniversalSectionEvaluation318.test_evaluation_bijective (q t) (e t) (section_eq t) b

lemma actual_representatives {T : Scheme} (b : T ⟶ FieldBase t) :
    Function.Surjective (relativeClass (pullback.snd (q t) b) (testSection t b)) :=
  RigidifiedRelativeClass318.relativeClass_surjective _ _
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b)

/-- On every full original test family, the quotient by actual base lines
is classified by rigidified actual lines up to a unique compatible actual
module-sheaf isomorphism. This is not effective fppf object descent. -/
theorem relative_eq_iff_unique_iso {T : Scheme} (b : T ⟶ FieldBase t)
    (L M : RigidifiedLine (testSection t b)) :
    relativeClass (pullback.snd (q t) b) (testSection t b) L =
      relativeClass (pullback.snd (q t) b) (testSection t b) M ↔
      ∃! _f : CompatibleIso (testSection t b) L M, True :=
  relative_eq_iff_unique_compatible _ _
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b)
    (test_evaluation_bijective t b) L M
end ContactUniversalRigidifiedClass318
