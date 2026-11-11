module
public import IntegralOverlapChartMaps318
public import ThreeRootCoordinates318
public section
noncomputable section
namespace ThreeRootScaledGenerators318
open QuadraticPresentation318 ThreeRootCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [CommRing S]

theorem root_scale_smul (a b : S) (y : Sˣ) (ha : IsUnit a) (h : b=a*(y:S)^2) :
    IntegralReciprocalRootScale318.rootEquiv a b y ha h (AdjoinRoot.root (polynomial b))=
      (y:S) • AdjoinRoot.root (polynomial a) := by
  rw [IntegralReciprocalRootScale318.rootEquiv_root,Algebra.smul_def]

/-- Evaluate the tensor equivalence before specializing to nested orders. -/
private lemma tensor_congr_tmul
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra S A] [Algebra S B] [Algebra S C] [Algebra S D]
    (f : A ≃ₐ[S] C) (g : B ≃ₐ[S] D) (a : A) (b : B) :
    Algebra.TensorProduct.congr f g (a ⊗ₜ[S] b) = f a ⊗ₜ[S] g b := by
  change Algebra.TensorProduct.map (f : A →ₐ[S] C) (g : B →ₐ[S] D)
    (a ⊗ₜ[S] b) = _
  exact Algebra.TensorProduct.map_tmul _ _ _ _

/-- Every individual original root has the same signed scaling law in the
actual threefold tensor order. No root permutation or sign quotient is used. -/
theorem order_scale (a b : Fin 3 → S) (y : Sˣ) (ha : ∀ j,IsUnit (a j))
    (h : ∀ j,b j=a j*(y:S)^2) (j : Fin 3) :
    IntegralReciprocalRootScale318.orderEquiv a b y ha h (generator b j)=
      (y:S) • generator a j := by
  let e₀ := IntegralReciprocalRootScale318.rootEquiv (a 0) (b 0) y (ha 0) (h 0)
  let e₁ := IntegralReciprocalRootScale318.rootEquiv (a 1) (b 1) y (ha 1) (h 1)
  let e₂ := IntegralReciprocalRootScale318.rootEquiv (a 2) (b 2) y (ha 2) (h 2)
  have h₀ : e₀ (AdjoinRoot.root (polynomial (b 0))) =
      (y:S) • AdjoinRoot.root (polynomial (a 0)) := root_scale_smul _ _ y (ha 0) (h 0)
  have h₁ : e₁ (AdjoinRoot.root (polynomial (b 1))) =
      (y:S) • AdjoinRoot.root (polynomial (a 1)) := root_scale_smul _ _ y (ha 1) (h 1)
  have h₂ : e₂ (AdjoinRoot.root (polynomial (b 2))) =
      (y:S) • AdjoinRoot.root (polynomial (a 2)) := root_scale_smul _ _ y (ha 2) (h 2)
  fin_cases j
  · change Algebra.TensorProduct.congr e₀ (Algebra.TensorProduct.congr e₁ e₂)
      (AdjoinRoot.root (polynomial (b 0)) ⊗ₜ[S]
        (1 : RootRing (b 1) ⊗[S] RootRing (b 2))) =
      (y:S) • (AdjoinRoot.root (polynomial (a 0)) ⊗ₜ[S]
        (1 : RootRing (a 1) ⊗[S] RootRing (a 2)))
    rw [tensor_congr_tmul,map_one]
    have ht := congrArg (fun t : RootRing (a 0) =>
      t ⊗ₜ[S] (1 : RootRing (a 1) ⊗[S] RootRing (a 2))) h₀
    simpa only [←TensorProduct.smul_tmul'] using ht
  · change Algebra.TensorProduct.congr e₀ (Algebra.TensorProduct.congr e₁ e₂)
      ((1 : RootRing (b 0)) ⊗ₜ[S]
        (AdjoinRoot.root (polynomial (b 1)) ⊗ₜ[S] (1 : RootRing (b 2)))) =
      (y:S) • ((1 : RootRing (a 0)) ⊗ₜ[S]
        (AdjoinRoot.root (polynomial (a 1)) ⊗ₜ[S] (1 : RootRing (a 2))))
    rw [tensor_congr_tmul,tensor_congr_tmul,map_one,map_one]
    have ht := congrArg (fun t : RootRing (a 1) =>
      (1 : RootRing (a 0)) ⊗ₜ[S] (t ⊗ₜ[S] (1 : RootRing (a 2)))) h₁
    simpa only [←TensorProduct.smul_tmul',TensorProduct.tmul_smul] using ht
  · change Algebra.TensorProduct.congr e₀ (Algebra.TensorProduct.congr e₁ e₂)
      ((1 : RootRing (b 0)) ⊗ₜ[S]
        ((1 : RootRing (b 1)) ⊗ₜ[S] AdjoinRoot.root (polynomial (b 2)))) =
      (y:S) • ((1 : RootRing (a 0)) ⊗ₜ[S]
        ((1 : RootRing (a 1)) ⊗ₜ[S] AdjoinRoot.root (polynomial (a 2))))
    rw [tensor_congr_tmul,tensor_congr_tmul,map_one,map_one]
    have ht := congrArg (fun t : RootRing (a 2) =>
      (1 : RootRing (a 0)) ⊗ₜ[S] ((1 : RootRing (a 1)) ⊗ₜ[S] t)) h₂
    simpa only [TensorProduct.tmul_smul] using ht

/-- Parameter transport fixes the literal root generators, not merely their
squares or the rank of the underlying module. -/
theorem parameter_generator (a b : Fin 3 → S) (h : ∀ j,a j=b j) (j : Fin 3) :
    IntegralReciprocalRootScale318.orderParameterEquiv a b h (generator a j)=generator b j := by
  fin_cases j <;>
    simp [IntegralReciprocalRootScale318.orderParameterEquiv,generator,
      Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
end ThreeRootScaledGenerators318
