module
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Action.Basic
public section
namespace OriginalR8FirstSlotSplitEqualizer318

universe u v w t
variable {K : Type u} [CommRing K] {I : Type v} {J : Type w} {G : Type t}

/-- Contravariant coordinate read of the literal first-slot map. -/
@[expose] def pull (p : I → J) : (J → K) →ₐ[K] (I → K) where
  toFun f := f ∘ p
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem pull_apply (p : I → J) (f : J → K) (i : I) : pull p f i = f (p i) := rfl

theorem injective_pull (p : I → J) (hsurj : Function.Surjective p) :
    Function.Injective (pull (K:=K) p) := by
  intro f h he
  funext j
  obtain ⟨i,rfl⟩ := hsurj j
  exact congrFun he i

/-- The full split coordinate equalizer of the specific first-slot orbit
map, not a rank calculation or a single field-point comparison. -/
theorem image_eq_fixed [SMul G I] (p : I → J) (hsurj : Function.Surjective p)
    (constant : ∀ (g : G) (i : I), p (g • i) = p i)
    (fibre : ∀ i j, p i = p j → ∃ g : G, g • i = j)
    (f : I → K) :
    (∀ (g : G) (i : I), f (g • i) = f i) ↔ ∃! a : J → K, pull p a = f := by
  classical
  constructor
  · intro h
    have hchoose := hsurj
    choose t ht using hchoose
    let a : J → K := fun j => f (t j)
    have he : pull p a = f := by
      funext i
      obtain ⟨g,hg⟩ := fibre (t (p i)) i (ht (p i))
      change f (t (p i)) = f i
      exact (h g (t (p i))).symm.trans (congrArg f hg)
    exact ⟨a,he,fun b hb => injective_pull p hsurj (hb.trans he.symm)⟩
  · rintro ⟨a,rfl,-⟩ g i
    exact congrArg a (constant g i)

end OriginalR8FirstSlotSplitEqualizer318
#print axioms OriginalR8FirstSlotSplitEqualizer318.pull_apply
#print axioms OriginalR8FirstSlotSplitEqualizer318.injective_pull
#print axioms OriginalR8FirstSlotSplitEqualizer318.image_eq_fixed
