module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public section
noncomputable section

namespace CTPadicAdicFiniteComplete318

open IsLocalRing
open scoped Topology TensorProduct

/-- The already complete p-adic integers have the exact maximal-ideal
adic topology, compared on the literal norm-ball basis. -/
theorem padic_adic_complete (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] := by
  have hp n : ((maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
      Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
    ext x
    change x ∈ (maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) ↔ _
    rw [PadicInt.maximalIdeal_eq_span_p,Ideal.span_singleton_pow,Metric.mem_closedBall,
      dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  have hA : IsAdic (maximalIdeal ℤ_[p]) := by
    apply isAdic_iff.2
    constructor
    · intro n
      rw [hp n]
      exact IsUltrametricDist.isOpen_closedBall _ (ne_of_gt
        (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _))
    · intro s hs
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨n,hn⟩ := PadicInt.exists_pow_neg_lt p hε
      refine ⟨n,?_⟩
      rw [hp n]
      exact (Metric.closedBall_subset_ball hn).trans hball
  exact hA.isAdicComplete_iff.2 ⟨inferInstance,inferInstance⟩

/-- Complete Noetherian base and finite module; no free-module
hypothesis. The produced map is the canonical adic-completion map. -/
theorem finite_module_complete {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) [IsAdicComplete I R] : IsAdicComplete I M := by
  let α : M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    (TensorProduct.lid R M).symm.trans
      (TensorProduct.congr (AdicCompletion.ofAlgEquiv I).toLinearEquiv (.refl R M))
  let β := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M
  let e := α.toEquiv.trans β.toEquiv
  have he : (⇑e) = AdicCompletion.of I M := by
    funext x
    change β (α x) = AdicCompletion.of I M x
    apply β.symm.injective
    rw [β.symm_apply_apply,AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of]
    change (TensorProduct.congr (AdicCompletion.ofAlgEquiv I).toLinearEquiv
      (LinearEquiv.refl R M)) ((TensorProduct.lid R M).symm x) = _
    simp only [TensorProduct.lid_symm_apply,TensorProduct.congr_tmul,
      AlgEquiv.coe_toLinearEquiv,map_one,LinearEquiv.refl_apply]
  exact (AdicCompletion.of_bijective_iff).1 (he ▸ e.bijective)

end CTPadicAdicFiniteComplete318
