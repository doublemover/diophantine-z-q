module
public import RigidifiedLineIsomorphism318
public section
noncomputable section
namespace RigidifiedRelativeClass318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RelativeLineClassQuotient318 RelativeLineSectionNormalization318 RigidifiedLineIsomorphism318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (hs : e ≫ p = 𝟙 S)

/-- The exact original quotient by base lines, with no degree restriction. -/
@[expose] def relativeClass (L : RigidifiedLine e) : RelativeClass p := classMap p (classOf L.line)

include hs in
lemma relative_eq_iff_class_eq (L M : RigidifiedLine e) :
    relativeClass p e L = relativeClass p e M ↔ classOf L.line = classOf M.line := by
  constructor
  · intro h
    change kernelToQuotient p e (kernelClass e L) = kernelToQuotient p e (kernelClass e M) at h
    have hk := congrArg (quotientToKernel p e hs) h
    rw [kernel_left_inverse, kernel_left_inverse] at hk
    exact congrArg Subtype.val hk
  · exact congrArg (classMap p)

include hs in
lemma relative_eq_iff_compatible (he : Function.Bijective e.appTop) (L M : RigidifiedLine e) :
    relativeClass p e L = relativeClass p e M ↔ Nonempty (CompatibleIso e L M) :=
  (relative_eq_iff_class_eq p e hs L M).trans (compatible_iff_class_eq e he L M).symm

include hs in
/-- Equal original relative classes have exactly one actual rigidification-
compatible isomorphism when global evaluation is bijective. -/
lemma relative_eq_iff_unique_compatible (he : Function.Bijective e.appTop) (L M : RigidifiedLine e) :
    relativeClass p e L = relativeClass p e M ↔ ∃! _f : CompatibleIso e L M, True := by
  rw [relative_eq_iff_compatible p e hs he]
  constructor
  · rintro ⟨f⟩
    exact ⟨f, trivial, fun g _ => compatible_unique e he.injective L M g f⟩
  · rintro ⟨f, _, _⟩
    exact ⟨f⟩

include hs in
lemma relativeClass_surjective : Function.Surjective (relativeClass p e) :=
  RelativeRigidifiedLine318.relativeClass_surjective p e hs
end RigidifiedRelativeClass318
