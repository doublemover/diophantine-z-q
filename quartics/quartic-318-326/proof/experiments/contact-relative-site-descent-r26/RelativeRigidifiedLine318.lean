module
public import RelativeLineSectionNormalization318
public section
noncomputable section
namespace RelativeRigidifiedLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open LineClassPullbackHom318 RelativeLineClassQuotient318
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X)

/-- A genuine original line together with an actual trivialization of its
restriction to the specified section. No degree condition is imposed. -/
structure RigidifiedLine where
  line : Line X
  trivialization : (LineSheafPullback318.line e line).object ≅
    (LineSheafUnit318.line S).object

/-- The actual original tensor/inverse/pullback construction, not an abstract
representative of a separately chosen group element. -/
@[expose] def normalizedLine (L : Line X) : Line X :=
  LineSheafTensor318.line L
    (FramedLineInverse318.inverse
      (LineSheafPullback318.line p (LineSheafPullback318.line e L)))

lemma normalizedLine_class (L : Line X) :
    classOf (normalizedLine p e L) =
      RelativeLineSectionNormalization318.normalize p e (classOf L) := by
  rw [normalizedLine, LineSheafClassGroup318.classOf_tensor,
    LineSheafClassGroup318.classOf_inverse]
  rfl

lemma normalizedLine_restriction_class (section_eq : e ≫ p = 𝟙 S) (L : Line X) :
    classOf (LineSheafPullback318.line e (normalizedLine p e L)) =
      classOf (LineSheafUnit318.line S) := by
  change pullback e (classOf (normalizedLine p e L)) = 1
  rw [normalizedLine_class]
  exact RelativeLineSectionNormalization318.normalize_at_section p e section_eq _

/-- The proved original class equality supplies an actual module-sheaf
isomorphism on the section. The noncomputable choice adds no descent premise. -/
@[expose] def normalizationTrivialization (section_eq : e ≫ p = 𝟙 S) (L : Line X) :
    (LineSheafPullback318.line e (normalizedLine p e L)).object ≅
      (LineSheafUnit318.line S).object :=
  Classical.choice ((classOf_eq_iff _ _).mp
    (normalizedLine_restriction_class p e section_eq L))

@[expose] def rigidifiedNormalization (section_eq : e ≫ p = 𝟙 S) (L : Line X) :
    RigidifiedLine e where
  line := normalizedLine p e L
  trivialization := normalizationTrivialization p e section_eq L

/-- Forgetting the specified trivialization lands in the exact original
section-restriction kernel, not the degree-zero subgroup. -/
@[expose] def kernelClass (L : RigidifiedLine e) : (pullback e).ker :=
  ⟨classOf L.line, classOf_eq L.trivialization⟩

lemma kernelClass_surjective : Function.Surjective (kernelClass e) := by
  intro c
  obtain ⟨L, hL⟩ := Quotient.exists_rep c.val
  change classOf L = c.val at hL
  have h : classOf (LineSheafPullback318.line e L) =
      classOf (LineSheafUnit318.line S) := by
    change pullback e (classOf L) = 1
    rw [hL]
    exact c.property
  refine ⟨⟨L, Classical.choice ((classOf_eq_iff _ _).mp h)⟩, ?_⟩
  exact Subtype.ext hL

lemma normalization_same_relative_class (section_eq : e ≫ p = 𝟙 S) (L : Line X) :
    classMap p (classOf (rigidifiedNormalization p e section_eq L).line) =
      classMap p (classOf L) := by
  change classMap p (classOf (normalizedLine p e L)) = _
  rw [normalizedLine_class]
  exact RelativeLineSectionNormalization318.quotient_normalize p e _

/-- Every original relative class has an actual section-rigidified line
representative once an actual section is supplied. -/
lemma relativeClass_surjective (section_eq : e ≫ p = 𝟙 S) :
    Function.Surjective (fun L : RigidifiedLine e => classMap p (classOf L.line)) := by
  intro c
  obtain ⟨d, rfl⟩ := classMap_surjective p c
  obtain ⟨L, rfl⟩ := Quotient.exists_rep d
  exact ⟨rigidifiedNormalization p e section_eq L,
    normalization_same_relative_class p e section_eq L⟩
end RelativeRigidifiedLine318
