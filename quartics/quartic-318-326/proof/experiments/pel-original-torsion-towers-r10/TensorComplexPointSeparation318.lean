module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace TensorComplexPointSeparation318
open scoped TensorProduct
variable {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

@[expose] def evaluation (f : A →ₐ[K] K) (g : B →ₐ[K] K) : A ⊗[K] B →ₐ[K] K :=
  Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)

lemma evaluation_smul (f : A →ₐ[K] K) (g : B →ₐ[K] K) (c : K) (x : A ⊗[K] B) :
    evaluation f g (c • x)=c • evaluation f g x :=
  (evaluation f g).toLinearMap.map_smul c x

@[expose] def contract (g : B →ₐ[K] K) : A ⊗[K] B →ₗ[K] A :=
  (TensorProduct.rid K A).toLinearMap.comp (g.toLinearMap.lTensor A)

lemma contract_tmul (g : B →ₐ[K] K) (a : A) (b : B) :
    contract g (a ⊗ₜ[K] b)=g b • a := by
  simp only [contract,LinearMap.comp_apply,LinearMap.lTensor_tmul,TensorProduct.rid_tmul]

lemma contract_evaluation (f : A →ₐ[K] K) (g : B →ₐ[K] K) (x : A ⊗[K] B) :
    f (contract g x)=evaluation f g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [contract_tmul,f.toLinearMap.map_smul]
    simp only [evaluation,Algebra.TensorProduct.lift_tmul,smul_eq_mul,mul_comm]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Separate genuine field-valued algebra points detect EVERY tensor,
not just pure tensors. A basis expansion is finite for each tensor;
no finite-dimensional or geometric-reducedness premise is hidden. -/
theorem eq_zero
    (hA : ∀ a : A, (∀ f : A →ₐ[K] K, f a=0) → a=0)
    (hB : ∀ b : B, (∀ g : B →ₐ[K] K, g b=0) → b=0)
    (x : A ⊗[K] B) (hx : ∀ f : A →ₐ[K] K, ∀ g : B →ₐ[K] K, evaluation f g x=0) : x=0 := by
  let b := Module.Free.chooseBasis K A
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  have hc (g : B →ₐ[K] K) : contract g x=0 := by
    apply hA
    intro f
    rw [contract_evaluation,hx]
  have he (g : B →ₐ[K] K) (i : Module.Free.ChooseBasisIndex K A) :
      g (e x i)=b.coord i (contract g x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero,Finsupp.zero_apply]
    | tmul a c =>
      change g (TensorProduct.equivFinsuppOfBasisLeft b (a ⊗ₜ[K] c) i)=_
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,contract_tmul,
        g.toLinearMap.map_smul,map_smul]
      change (b.repr a i)*g c=g c*(b.repr a i)
      exact mul_comm _ _
    | add y z hy hz => simp only [map_add,Finsupp.add_apply,hy,hz]
  apply e.injective
  ext i
  change e x i=0
  apply hB
  intro g
  rw [he,hc,map_zero]

theorem ext
    (hA : ∀ a : A, (∀ f : A →ₐ[K] K, f a=0) → a=0)
    (hB : ∀ b : B, (∀ g : B →ₐ[K] K, g b=0) → b=0)
    (x y : A ⊗[K] B)
    (h : ∀ f : A →ₐ[K] K, ∀ g : B →ₐ[K] K, evaluation f g x=evaluation f g y) : x=y := by
  apply sub_eq_zero.mp
  apply eq_zero hA hB
  intro f g
  rw [map_sub,h f g,sub_self]
end TensorComplexPointSeparation318
