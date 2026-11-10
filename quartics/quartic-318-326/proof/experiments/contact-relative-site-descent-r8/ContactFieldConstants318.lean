module
public import ProperChartConstants318
public import ContactFieldAffineChart318
public section
noncomputable section
namespace ContactFieldConstants318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)

lemma swapped_constant_bijective : Function.Bijective
    (ProperChartConstants318.structuralMap (ContactFieldAffineChart318.structureMap K c)) :=
  ProperChartConstants318.constant_bijective _
    (ContactFieldAffineChart318.chart K c) (ContactFieldAffineChart318.chart_over K c)

/-- The original source-first fiber product, matching the relative Picard
and actual contact-section family, without selecting a component. -/
abbrev Family := pullback (ContactFieldAffineChart318.sourceStructure c)
  (ContactFieldAffineChart318.fieldMap K)
abbrev structureMap : Family K c ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
abbrev structuralMap := ProperChartConstants318.structuralMap (structureMap K c)

/-- Every global regular function on the whole original field base change
is exactly one structural K structuralMap. -/
theorem constant_bijective : Function.Bijective (structuralMap K c) := by
  let e := pullbackSymmetry (ContactFieldAffineChart318.sourceStructure c)
    (ContactFieldAffineChart318.fieldMap K)
  have he : e.hom ≫ ContactFieldAffineChart318.structureMap K c = structureMap K c := by
    simp [e, ContactFieldAffineChart318.structureMap, structureMap]
  have h : (structuralMap K c : K → Γ(Family K c, ⊤)) =
      e.hom.appTop ∘ ProperChartConstants318.structuralMap
        (ContactFieldAffineChart318.structureMap K c) := by
    funext a
    exact (StructuralConstantPullback318.app_constant e.hom _ _ he a).symm
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp (swapped_constant_bijective K c)

@[expose] def constantsIso : K ≃+* Γ(Family K c, ⊤) :=
  RingEquiv.ofBijective (structuralMap K c) (constant_bijective K c)

@[simp] lemma constantsIso_apply (a : K) : constantsIso K c a = structuralMap K c a := rfl

/-- The actual value at any field-valued point is faithful on these actual
global functions. No assumption of a K-rational point is made. -/
lemma fieldPoint_appTop_injective {F : Type} [Field F]
    (p : Spec (CommRingCat.of F) ⟶ Family K c) : Function.Injective p.appTop := by
  intro a b h
  obtain ⟨q, rfl⟩ := (constant_bijective K c).surjective a
  obtain ⟨r, rfl⟩ := (constant_bijective K c).surjective b
  let e : K →+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
    (p.appTop.hom.comp (structuralMap K c))
  have he : e q = e r := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom h
  exact congrArg (structuralMap K c) (e.injective he)
end ContactFieldConstants318
