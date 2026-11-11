module
public import OriginalAffineCoefficientCover318
public section
noncomputable section
namespace LocalImageCoverDescent318
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
/-- Covering after each generator of an actual covering family suffices;
the proof explicitly retains arbitrary arrows factoring through them. -/
lemma sieve_of_cover {X : C} {I : Type*} (Y : I → C) (f : ∀ i,Y i ⟶ X)
    (hc : Sieve.ofArrows Y f ∈ J X) (V : Sieve X)
    (h : ∀ i,V.pullback (f i) ∈ J (Y i)) : V ∈ J X := by
  apply J.transitive hc V
  intro Z g hg
  obtain ⟨i,k,rfl⟩ := Sieve.ofArrows.exists hg
  rw [Sieve.pullback_comp]
  exact J.pullback_stable k (h i)
/-- A local-image property for all values of a locally surjective map
extends to EVERY target sheaf element, through the actual image sieve.
No surjectivity of individual components or unit injectivity is used. -/
lemma from_local_source {F G H : Cᵒᵖ ⥤ Type w} (a : F ⟶ H) (u : G ⟶ H)
    [Presheaf.IsLocallySurjective J u]
    (h : ∀ (X : C) (x : G.obj (op X)),Presheaf.imageSieve a (u.app (op X) x) ∈ J X) :
    Presheaf.IsLocallySurjective J a where
  imageSieve_mem {X} y := by
    apply J.transitive (Presheaf.imageSieve_mem J u y) (Presheaf.imageSieve a y)
    intro Y f hf
    obtain ⟨x,hx⟩ := hf
    rw [Presheaf.pullback_imageSieve,←hx]
    exact h Y x
end LocalImageCoverDescent318
