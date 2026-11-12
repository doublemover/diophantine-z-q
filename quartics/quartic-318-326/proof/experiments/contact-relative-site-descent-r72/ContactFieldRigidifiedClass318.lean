module
public import RigidifiedRelativeClass318
public import ContactFieldConstants318
public import ContactFieldSection318
public section
noncomputable section
namespace ContactFieldRigidifiedClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (t : ℚ)
abbrev K := ContactFieldSection318.L c t
abbrev X := ContactFieldConstants318.Family (K c t) c
abbrev p : X c t ⟶ Spec (CommRingCat.of (K c t)) :=
  ContactFieldConstants318.structureMap (K c t) c
abbrev e : Spec (CommRingCat.of (K c t)) ⟶ X c t := ContactFieldSection318.pointSection c t

lemma section_eq : e c t ≫ p c t = 𝟙 _ := ContactFieldSection318.pointSection_snd c t

/-- The actual section evaluation is bijective on actual global functions,
using the proved full field-family constants and exact section equality. -/
lemma section_appTop_bijective : Function.Bijective (e c t).appTop := by
  refine ⟨ContactFieldConstants318.fieldPoint_appTop_injective (K c t) c (e c t), ?_⟩
  intro s
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (K c t))).inv).surjective s
  refine ⟨ProperChartConstants318.structuralMap (p c t) a, ?_⟩
  have h := StructuralConstantPullback318.app_constant (e c t) (𝟙 _) (p c t) (section_eq c t) a
  exact h.trans ha

/-- Every original relative class has an actual line with an actual
trivialization on the exact contact section. -/
lemma actual_representatives : Function.Surjective (relativeClass (p c t) (e c t)) :=
  RigidifiedRelativeClass318.relativeClass_surjective (p c t) (e c t) (section_eq c t)

/-- Two rigidified original lines on the entire contact field family have
the same original relative class exactly when there is one and only one
actual isomorphism respecting their specified trivializations. -/
theorem relative_eq_iff_unique_iso (L M : RigidifiedLine (e c t)) :
    relativeClass (p c t) (e c t) L = relativeClass (p c t) (e c t) M ↔
      ∃! _f : CompatibleIso (e c t) L M, True :=
  relative_eq_iff_unique_compatible (p c t) (e c t) (section_eq c t)
    (section_appTop_bijective c t) L M
end ContactFieldRigidifiedClass318
