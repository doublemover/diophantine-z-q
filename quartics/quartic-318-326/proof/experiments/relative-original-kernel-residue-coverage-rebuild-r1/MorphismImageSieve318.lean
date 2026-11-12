module
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public section
noncomputable section
namespace MorphismImageSieve318
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] {X B T U : C}
/-- The actual categorical image sieve of one specified morphism. It
records factorizations, not surjectivity on underlying topological points. -/
@[expose] def image (f : X ⟶ B) : Sieve B where
  arrows T g := ∃ h : T ⟶ X, h ≫ f=g
  downward_closed := by
    rintro Y Z g ⟨h,rfl⟩ k
    exact ⟨k ≫ h,Category.assoc _ _ _⟩
lemma membership (f : X ⟶ B) (g : T ⟶ B) :
    image f g ↔ ∃ h : T ⟶ X, h ≫ f=g := Iff.rfl
lemma generated (f : X ⟶ B) :
    image f=Sieve.ofArrows (fun _ : PUnit => X) (fun _ => f) := by
  ext T g
  rw [membership,Sieve.mem_ofArrows_iff]
  exact ⟨fun ⟨h,hh⟩ => ⟨PUnit.unit,h,hh.symm⟩,
    fun ⟨_,h,hh⟩ => ⟨h,hh.symm⟩⟩
lemma self (f : X ⟶ B) : image f f := ⟨𝟙 X,Category.id_comp f⟩
/-- Literal pullback of the actual image sieve equals the image of the
actual categorical pullback projection, without any flatness premise. -/
lemma pullback_image (f : X ⟶ B) (g : T ⟶ B) [HasPullback f g] :
    (image f).pullback g=image (pullback.snd f g) := by
  ext U h
  change (∃ k : U ⟶ X, k ≫ f=h ≫ g) ↔
    ∃ k : U ⟶ pullback f g, k ≫ pullback.snd f g=h
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨pullback.lift k h hk,pullback.lift_snd _ _ _⟩
  · rintro ⟨k,rfl⟩
    exact ⟨k ≫ pullback.fst f g,by simp only [Category.assoc,pullback.condition]⟩
end MorphismImageSieve318
