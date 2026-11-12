module
public import SplitKernelBaseChange318
public import Mathlib.RingTheory.Flat.Basic
public section
noncomputable section
namespace FlatKernelBaseChange318
open TensorProduct
open scoped TensorProduct
universe u v w z
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (B : Type w) [AddCommGroup B] [Module R B] (d : A →ₗ[R] B)
  (S : Type z) [CommRing S] [Algebra R S] [hflat : Module.Flat R S]

include hflat
/-- Tensoring the ACTUAL kernel inclusion is injective because the new
coefficient algebra is flat. No surjectivity or splitting of d is assumed. -/
lemma injective : Function.Injective (SplitKernelBaseChange318.map R A B d S) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M:=S) (LinearMap.ker d).subtype Subtype.val_injective
  exact congrArg Subtype.val h

lemma surjective : Function.Surjective (SplitKernelBaseChange318.map R A B d S) := by
  have he : Function.Exact (LinearMap.ker d).subtype d := by
    rw [LinearMap.exact_iff]
    ext x
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩
  have ht := Module.Flat.lTensor_exact (M:=S) he
  intro z
  have hz : z.val∈LinearMap.ker (d.lTensor S) := z.property
  rw [LinearMap.exact_iff.mp ht] at hz
  obtain ⟨x,hx⟩ := hz
  exact ⟨x,Subtype.ext hx⟩

/-- Flat base change commutes with the WHOLE original kernel, with its
literal inclusion and actual pure tensor formula. -/
@[expose] def equivalence : S ⊗[R] LinearMap.ker d ≃ₗ[S] LinearMap.ker (d.baseChange S) :=
  LinearEquiv.ofBijective (SplitKernelBaseChange318.map R A B d S)
    ⟨injective R A B d S,surjective R A B d S⟩
lemma coe (x : S ⊗[R] LinearMap.ker d) :
    (equivalence R A B d S x).val=(LinearMap.ker d).subtype.baseChange S x := rfl
lemma tmul (s : S) (x : LinearMap.ker d) :
    (equivalence R A B d S (s ⊗ₜ[R] x)).val=s ⊗ₜ[R] x.val := rfl
end FlatKernelBaseChange318
