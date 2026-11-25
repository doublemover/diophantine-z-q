module
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public section
noncomputable section

namespace OriginalR8WildFixedFlatBase318

open scoped TensorProduct
open TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t
variable {A : Type u} {B : Type v} {C : Type w} {G : Type t}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- The genuine defect of a fixed equation, coordinate by coordinate.
The finite list is the full original group acting on the actual
normal arithmetic order. No averaging operator is constructed. -/
@[expose] def defect (σ : G → B ≃ₐ[A] B) : B →ₗ[A] (G → B) :=
  LinearMap.pi fun g => (σ g).toLinearMap - LinearMap.id

theorem defect_exact (σ : G → B ≃ₐ[A] B)
    (hfixed : ∀ b : B, (∀ g : G, σ g b = b) ↔ ∃ a : A, algebraMap A B a = b) :
    Function.Exact (Algebra.linearMap A B) (defect σ) := by
  intro b
  change defect σ b = 0 ↔ ∃ a : A, algebraMap A B a = b
  refine (?_ : defect σ b = 0 ↔ ∀ g : G, σ g b = b).trans (hfixed b)
  constructor
  · intro h g
    have hg : σ g b - b = 0 := congrFun h g
    exact sub_eq_zero.mp hg
  · intro h
    funext g
    change σ g b - b = 0
    exact sub_eq_zero.mpr (h g)

variable [Fintype G] [DecidableEq G]

abbrev pieces := TensorProduct.piRight A C C (fun _ : G => B)

theorem defect_piece (σ : G → B ≃ₐ[A] B) (z : C ⊗[A] B) (g : G) :
    pieces ((defect σ).lTensor C z) g = ((σ g).toLinearMap.lTensor C) z - z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.lTensor_tmul]
    change c ⊗ₜ[A] (σ g b - b) = (c ⊗ₜ[A] σ g b) - (c ⊗ₜ[A] b)
    exact TensorProduct.tmul_sub _ _ _
  | add x y hx hy =>
    rw [map_add, map_add]
    change pieces ((defect σ).lTensor C x) g + pieces ((defect σ).lTensor C y) g = _
    rw [hx,hy,map_add]
    exact (add_sub_add_comm _ _ _ _).symm

/-- Flat extension of the same order, notably to its actual completion:
an element fixed by the full actual action is precisely c⊗1. This is
the literal flat equalizer, including residual characteristic |G|. -/
theorem fixed_after_flat [Module.Flat A C] (σ : G → B ≃ₐ[A] B)
    (hfixed : ∀ b : B, (∀ g : G, σ g b = b) ↔ ∃ a : A, algebraMap A B a = b)
    (z : C ⊗[A] B) :
    (∀ g : G, ((σ g).toLinearMap.lTensor C) z = z) ↔
      ∃ c : C, (c ⊗ₜ[A] (1 : B)) = z := by
  have hz : (∀ g : G, ((σ g).toLinearMap.lTensor C) z = z) ↔
      (defect σ).lTensor C z = 0 := by
    constructor
    · intro h
      apply pieces.injective
      funext g
      simp only [defect_piece σ z g,h g,sub_self,map_zero,Pi.zero_apply]
    · intro h g
      have h' := defect_piece σ z g
      rw [h,map_zero] at h'
      exact sub_eq_zero.mp h'.symm
  let f := Algebra.linearMap A B
  have exactT : Function.Exact (f.lTensor C) ((defect σ).lTensor C) :=
    Module.Flat.lTensor_exact C (defect_exact σ hfixed)
  refine hz.trans ((exactT z).trans ?_)
  constructor
  · rintro ⟨r,hr⟩
    let c := TensorProduct.rid A C r
    have hrc : r = c ⊗ₜ[A] (1:A) := by
      apply (TensorProduct.rid A C).injective
      simp only [TensorProduct.rid_tmul,one_smul,c]
    refine ⟨c,?_⟩
    rw [hrc,LinearMap.lTensor_tmul] at hr
    simpa only [f,Algebra.linearMap_apply,map_one] using hr
  · rintro ⟨c,hc⟩
    exact ⟨c ⊗ₜ[A] (1:A),by simpa only [LinearMap.lTensor_tmul,f,Algebra.linearMap_apply,map_one] using hc⟩

end OriginalR8WildFixedFlatBase318

#print axioms OriginalR8WildFixedFlatBase318.defect_exact
#print axioms OriginalR8WildFixedFlatBase318.defect_piece
#print axioms OriginalR8WildFixedFlatBase318.fixed_after_flat
