module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public section
noncomputable section
namespace SplitKernelBaseChange318
open TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 750000
universe u v w z
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (B : Type w) [AddCommGroup B] [Module R B]
  (d : A →ₗ[R] B) (s : B →ₗ[R] A) (hs : d.comp s = LinearMap.id)

@[expose] def retraction : A →ₗ[R] LinearMap.ker d :=
  (LinearMap.id-s.comp d).codRestrict (LinearMap.ker d) (by
    intro x
    change d (x-s (d x)) = 0
    rw [map_sub,← LinearMap.comp_apply,hs,LinearMap.id_apply,sub_self])

lemma retract (x : LinearMap.ker d) : retraction R A B d s hs x = x := by
  apply Subtype.ext
  change (x : A)-s (d x) = x
  rw [x.property,map_zero,sub_zero]

lemma identity (x : A) : (retraction R A B d s hs x : A) = x-s (d x) := rfl

include hs in
/-- A split kernel is projective when its actual source is projective.
Neither finiteness nor a basis of that kernel is inferred. -/
theorem projective [Module.Projective R A] : Module.Projective R (LinearMap.ker d) :=
  Module.Projective.of_split (LinearMap.ker d).subtype (retraction R A B d s hs) (by
    ext x
    exact retract R A B d s hs x)

variable (S : Type z) [CommRing S] [Algebra R S]

lemma extended_zero (x : S ⊗[R] LinearMap.ker d) :
    d.baseChange S (((LinearMap.ker d).subtype.baseChange S) x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a k =>
    change a ⊗ₜ[R] d (k : A) = 0
    rw [k.property,tmul_zero]
  | add x y hx hy => simpa only [map_add,hx,hy,add_zero]

/-- The actual tensor of the original kernel inclusion. -/
@[expose] def map : S ⊗[R] LinearMap.ker d →ₗ[S] LinearMap.ker (d.baseChange S) :=
  ((LinearMap.ker d).subtype.baseChange S).codRestrict (LinearMap.ker (d.baseChange S))
    (extended_zero R A B d S)

@[expose] def inverse : LinearMap.ker (d.baseChange S) →ₗ[S] S ⊗[R] LinearMap.ker d :=
  ((retraction R A B d s hs).baseChange S).comp (LinearMap.ker (d.baseChange S)).subtype

lemma inverse_map (x : S ⊗[R] LinearMap.ker d) :
    inverse R A B d s hs S (map R A B d S x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a k =>
    change a ⊗ₜ[R] retraction R A B d s hs (k : A) = a ⊗ₜ[R] k
    rw [retract]
  | add x y hx hy => simpa only [map_add,hx,hy]

lemma extended_identity (x : S ⊗[R] A) :
    (LinearMap.ker d).subtype.baseChange S ((retraction R A B d s hs).baseChange S x) =
      x-s.baseChange S (d.baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change a ⊗ₜ[R] (retraction R A B d s hs x : A) = a ⊗ₜ[R] x-a ⊗ₜ[R] s (d x)
    rw [identity,tmul_sub]
  | add x y hx hy =>
    simp only [map_add,hx,hy]
    abel

lemma map_inverse (x : LinearMap.ker (d.baseChange S)) :
    map R A B d S (inverse R A B d s hs S x) = x := by
  apply Subtype.ext
  change (LinearMap.ker d).subtype.baseChange S ((retraction R A B d s hs).baseChange S x) = x
  rw [extended_identity,x.property,map_zero,sub_zero]

/-- Arbitrary coefficient base change preserves this genuine kernel
because its exact sequence SPLITS, not because tensor is left exact. -/
@[expose] def equivalence : S ⊗[R] LinearMap.ker d ≃ₗ[S] LinearMap.ker (d.baseChange S) where
  __ := map R A B d S
  invFun := inverse R A B d s hs S
  left_inv := inverse_map R A B d s hs S
  right_inv := map_inverse R A B d s hs S

/-- Projectivity of the target produces the needed splitting only on
the actual surjective/vanishing locus. -/
theorem exists_splitting [Module.Projective R B] (hd : Function.Surjective d) :
    ∃ s : B →ₗ[R] A, d.comp s = LinearMap.id :=
  Module.projective_lifting_property d LinearMap.id hd
end SplitKernelBaseChange318
