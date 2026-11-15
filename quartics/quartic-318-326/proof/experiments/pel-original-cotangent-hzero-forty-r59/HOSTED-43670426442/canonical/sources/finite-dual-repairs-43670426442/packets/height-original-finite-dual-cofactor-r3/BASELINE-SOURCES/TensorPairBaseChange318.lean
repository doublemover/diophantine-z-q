module
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic
public section
noncomputable section
namespace TensorPairBaseChange318
set_option maxHeartbeats 800000
open scoped TensorProduct
variable (R S A B:Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Actual base change commutes with the binary tensor product, with both
copies of the new base multiplied by the genuine algebra map. -/
@[expose] def merge : (S⊗[R]A)⊗[S](S⊗[R]B) ≃ₐ[S] S⊗[R](A⊗[R]B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R S S S A S B).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid S S)
      (AlgEquiv.refl : A⊗[R]B ≃ₐ[R] A⊗[R]B))

@[simp] theorem merge_tmul (s t:S) (a:A) (b:B) :
    merge R S A B ((s⊗ₜ[R]a)⊗ₜ[S](t⊗ₜ[R]b))=(s*t)⊗ₜ[R](a⊗ₜ[R]b) := by
  simp [merge]

@[simp] theorem split_one (a:A) (b:B) :
    (merge R S A B).symm (1⊗ₜ[R](a⊗ₜ[R]b))=
      (1⊗ₜ[R]a)⊗ₜ[S](1⊗ₜ[R]b) := by
  apply (merge R S A B).injective
  simp

variable {R S A B} {A' B':Type*} [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

@[expose] def tensorEquiv (f:S⊗[R]A≃ₐ[S]S⊗[R]A') (g:S⊗[R]B≃ₐ[S]S⊗[R]B') :
    S⊗[R](A⊗[R]B) ≃ₐ[S] S⊗[R](A'⊗[R]B') :=
  (merge R S A B).symm.trans ((Algebra.TensorProduct.congr f g).trans (merge R S A' B'))

/-- The constructed equivalence agrees on every original order element with
the actual tensor-product homomorphism. -/
theorem tensorEquiv_on_order (f:S⊗[R]A≃ₐ[S]S⊗[R]A') (g:S⊗[R]B≃ₐ[S]S⊗[R]B')
    (φ:A→ₐ[R]A') (ψ:B→ₐ[R]B')
    (hf:∀a,f (1⊗ₜ[R]a)=1⊗ₜ[R]φ a) (hg:∀b,g (1⊗ₜ[R]b)=1⊗ₜ[R]ψ b)
    (z:A⊗[R]B) :
    tensorEquiv f g (1⊗ₜ[R]z)=1⊗ₜ[R]Algebra.TensorProduct.map φ ψ z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb=>simp only [TensorProduct.tmul_add,map_add,ha,hb]
  | tmul a b=>simp [tensorEquiv,split_one,hf,hg]

end TensorPairBaseChange318
