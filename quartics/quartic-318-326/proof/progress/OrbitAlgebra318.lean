module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

noncomputable section

namespace OrbitAlgebra318

variable (R G X : Type*) [CommRing R] [Group G] [MulAction G X]

/-- The actual invariant subalgebra of the split finite cover. -/
def fixedFunctions : Subalgebra R (X → R) where
  carrier := {f | ∀ (g : G) (x : X), f (g • x) = f x}
  mul_mem' hf hh g x := by simp only [Pi.mul_apply, hf g x, hh g x]
  one_mem' := by simp
  add_mem' hf hh g x := by simp only [Pi.add_apply, hf g x, hh g x]
  zero_mem' := by simp
  algebraMap_mem' r := by simp

abbrev Orbits := Quotient (MulAction.orbitRel G X)

/-- Functions on the orbit set are exactly the invariant coordinate algebra.
No division by the group order is used. -/
def orbitEquiv : (Orbits G X → R) ≃ₐ[R] fixedFunctions R G X where
  toFun f := ⟨fun x => f ⟦x⟧, by
    intro g x
    exact congrArg f (Quotient.sound ⟨g, rfl⟩)⟩
  invFun f := Quotient.lift f.1 (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact f.2 g y)
  left_inv f := by funext q; induction q using Quotient.inductionOn with | h x => rfl
  right_inv f := by ext x; rfl
  map_mul' f h := by ext x; rfl
  map_add' f h := by ext x; rfl
  commutes' r := by apply Subtype.ext; funext x; rfl

@[simp] theorem orbitEquiv_apply (f : Orbits G X → R) (x : X) :
    (orbitEquiv R G X f).1 x = f ⟦x⟧ := rfl

instance [Finite X] : Algebra.Etale R (fixedFunctions R G X) :=
  Algebra.Etale.of_equiv (orbitEquiv R G X)

instance [Finite X] : Module.Finite R (fixedFunctions R G X) :=
  Module.Finite.equiv (orbitEquiv R G X).toLinearEquiv

/-- The invariant algebra is finite étale even in characteristics dividing |G|. -/
theorem finite_etale [Finite X] :
    Module.Finite R (fixedFunctions R G X) ∧ Algebra.Etale R (fixedFunctions R G X) :=
  ⟨inferInstance, inferInstance⟩

end OrbitAlgebra318
