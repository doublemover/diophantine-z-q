module
public import ProjectiveFiberwiseCokernelFlat318
public section
noncomputable section
namespace ProjectiveFiberwiseInjection318
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- The fieldwise criterion already proves universal tensor injectivity;
in particular it proves injectivity of the ORIGINAL map over the full
possibly nonreduced coefficient ring, not only over residue fields. -/
lemma injective (f : A →ₗ[R] B)
    [Module.Projective R A] [Module.Projective R B]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (f.baseChange (R ⧸ m))) : Function.Injective f := by
  have hi := ProjectiveFiberwiseCokernelFlat318.tensor_injective f hf R
  intro a b hab
  have ht : (1:R) ⊗ₜ[R] a=(1:R) ⊗ₜ[R] b := hi (by
    simpa only [LinearMap.lTensor_tmul] using congrArg (fun x => (1:R) ⊗ₜ[R] x) hab)
  have he := congrArg (TensorProduct.lid R A) ht
  simpa only [TensorProduct.lid_tmul,one_smul] using he
end ProjectiveFiberwiseInjection318
