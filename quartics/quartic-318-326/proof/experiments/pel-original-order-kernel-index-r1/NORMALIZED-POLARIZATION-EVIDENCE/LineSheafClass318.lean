module
public import ModuleFreeOpenFrames318
public section
noncomputable section
namespace LineSheafClass318
open AlgebraicGeometry CategoryTheory
universe u
/-- An original module sheaf with genuine rank-one frames on a covering family.
The presentation is data; equivalence below forgets it only via actual sheaf isomorphism. -/
structure Line (X : Scheme.{u}) where
  object : X.Modules
  Index : Type u
  opens : Index → X.Opens
  cover : (⊤ : X.Opens) ≤ ⨆ i, opens i
  frame : ∀ i, SheafOfModules.unit (opens i).toScheme.ringCatSheaf ≅
    object.restrict (opens i).ι
/-- No presentation equality is required: this is the original module-sheaf relation. -/
abbrev Related {X : Scheme.{u}} (L N : Line X) : Prop := Nonempty (L.object ≅ N.object)
instance lineSetoid (X : Scheme.{u}) : Setoid (Line X) where
  r := Related
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩
/-- Isomorphism classes of the original framed line sheaves, not a Picard scheme
or a group structure. -/
@[expose] def Class (X : Scheme.{u}) := Quotient (lineSetoid X)
@[expose] def classOf {X : Scheme.{u}} (L : Line X) : Class X := Quotient.mk _ L
lemma classOf_eq_iff {X : Scheme.{u}} (L N : Line X) :
    classOf L = classOf N ↔ Nonempty (L.object ≅ N.object) :=
  Quotient.eq
lemma classOf_eq {X : Scheme.{u}} {L N : Line X} (e : L.object ≅ N.object) :
    classOf L = classOf N := Quotient.sound ⟨e⟩
lemma induction {X : Scheme.{u}} {P : Class X → Prop}
    (h : ∀ L, P (classOf L)) (c : Class X) : P c := Quotient.inductionOn c h
end LineSheafClass318
