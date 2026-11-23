module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Trace.Basic

public section
noncomputable section
open scoped TensorProduct

namespace SelectedJOneCRTTrace318

private theorem trace_quotient_mk {R C : Type*} [CommRing R] [CommRing C]
    [Algebra R C] [Module.Free R C] [Module.Finite R C] (I : Ideal R) (c : C) :
    Algebra.trace (R ⧸ I) (C ⧸ I.map (algebraMap R C))
      (Ideal.Quotient.mk (I.map (algebraMap R C)) c) =
      Ideal.Quotient.mk I (Algebra.trace R C c) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  rw [← Algebra.trace_eq_of_algEquiv e]
  change Algebra.trace (R ⧸ I) ((R ⧸ I) ⊗[R] C) (1 ⊗ₜ[R] c) = _
  rw [Algebra.trace_apply]
  have hmul :
      (Algebra.lmul (R ⧸ I) ((R ⧸ I) ⊗[R] C) (1 ⊗ₜ[R] c)) =
        (Algebra.lmul R C c).baseChange (R ⧸ I) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a b
    rw [LinearMap.baseChange_tmul]
    change (1 ⊗ₜ[R] c) * (a ⊗ₜ[R] b) = a ⊗ₜ[R] (c * b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hmul]
  exact LinearMap.trace_baseChange (Algebra.lmul R C c) (R ⧸ I)

/-- Lift the actual CRT idempotent (1,0). Its trace modulo the
arbitrary base ideal is the positive rank of the selected CRT factor.
The complement can be the zero ring. -/
theorem exists_selected_trace {R C : Type*} [CommRing R] [IsLocalRing R] [CommRing C]
    [Algebra R C] [Module.Free R C] [Module.Finite R C]
    (I : Ideal R) (P Q : Ideal C) (hI : I ≠ ⊤) (hP : P ≠ ⊤)
    (hcop : IsCoprime P Q) (hmul : P * Q = I.map (algebraMap R C)) :
    ∃ c : C, c ∈ Q ∧ Ideal.Quotient.mk P c = 1 ∧
      ∃ r : ℕ, 0 < r ∧ r ≤ Module.finrank R C ∧
        Ideal.Quotient.mk I (Algebra.trace R C c) = (↑r : R ⧸ I) := by
  let A := R ⧸ I
  let T := C ⧸ I.map (algebraMap R C)
  let D := C ⧸ P
  let E := C ⧸ Q
  letI : Nontrivial A := (Ideal.Quotient.nontrivial_iff).2 hI
  letI : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : Nontrivial D := (Ideal.Quotient.nontrivial_iff).2 hP
  have hleft : I.map (algebraMap R C) ≤ P := by
    rw [← hmul]
    exact Ideal.mul_le_left
  have hright : I.map (algebraMap R C) ≤ Q := by
    rw [← hmul]
    exact Ideal.mul_le_right
  letI : Algebra A D :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hleft)
  letI : Algebra A E :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hright)
  let e₀ : T ≃+* D × E :=
    (Ideal.quotEquivOfEq hmul.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hcop)
  have e_mk (c : C) :
      e₀ (Ideal.Quotient.mk (I.map (algebraMap R C)) c) =
        (Ideal.Quotient.mk P c, Ideal.Quotient.mk Q c) := by
    apply Prod.ext
    · simp only [e₀, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
    · simp only [e₀, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
  let e : T ≃ₐ[A] D × E :=
    { __ := e₀
      commutes' := by
        intro a
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
        change e₀ (Ideal.Quotient.mk (I.map (algebraMap R C)) (algebraMap R C r)) =
          (Ideal.Quotient.mk P (algebraMap R C r), Ideal.Quotient.mk Q (algebraMap R C r))
        exact e_mk (algebraMap R C r) }
  let q : T ≃ₐ[A] A ⊗[R] C := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  letI : Module.Free A T := Module.Free.of_equiv q.symm.toLinearEquiv
  letI : Module.Finite A T := Module.Finite.of_surjective q.symm.toLinearEquiv.toLinearMap q.symm.surjective
  letI : Module.Free A (D × E) := Module.Free.of_equiv e.toLinearEquiv
  letI : Module.Finite A (D × E) := Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  letI : Module.Finite A D := Module.Finite.of_surjective (LinearMap.fst A D E)
    (fun d => ⟨(d, 0), rfl⟩)
  letI : Module.Finite A E := Module.Finite.of_surjective (LinearMap.snd A D E)
    (fun x => ⟨(0, x), rfl⟩)
  letI : Module.Flat A D := Module.Flat.of_retract (LinearMap.inl A D E) (LinearMap.fst A D E)
    (LinearMap.ext fun _ => rfl)
  letI : Module.Flat A E := Module.Flat.of_retract (LinearMap.inr A D E) (LinearMap.snd A D E)
    (LinearMap.ext fun _ => rfl)
  letI : Module.Free A D := Module.free_of_flat_of_isLocalRing
  letI : Module.Free A E := Module.free_of_flat_of_isLocalRing
  obtain ⟨c, hc⟩ :=
    Ideal.Quotient.mk_surjective (I := I.map (algebraMap R C)) (e.symm (1, 0))
  have hsplit : e (Ideal.Quotient.mk (I.map (algebraMap R C)) c) = (1, 0) := by
    rw [hc, e.apply_symm_apply]
  have hread : (Ideal.Quotient.mk P c, Ideal.Quotient.mk Q c) = (1, 0) :=
    (e_mk c).symm.trans hsplit
  have hcP : Ideal.Quotient.mk P c = 1 := congrArg Prod.fst hread
  have hcQ : Ideal.Quotient.mk Q c = 0 := congrArg Prod.snd hread
  have htotal : Module.finrank A (D × E) = Module.finrank R C :=
    e.toLinearEquiv.finrank_eq.symm.trans
      (q.toLinearEquiv.finrank_eq.trans Module.finrank_baseChange)
  have hbound : Module.finrank A D ≤ Module.finrank R C := by
    rw [← htotal, Module.finrank_prod]
    exact Nat.le_add_right _ _
  have htrOne : Algebra.trace A D (1 : D) = (↑(Module.finrank A D) : A) := by
    simpa only [map_one, nsmul_eq_mul, mul_one] using
      (Algebra.trace_algebraMap (R := A) (S := D) (1 : A))
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp hcQ, hcP, Module.finrank A D,
    (Module.finrank_pos_iff_of_free A D).2 inferInstance, hbound, ?_⟩
  calc
    Ideal.Quotient.mk I (Algebra.trace R C c) =
        Algebra.trace A T (Ideal.Quotient.mk (I.map (algebraMap R C)) c) :=
      (trace_quotient_mk I c).symm
    _ = Algebra.trace A (D × E) (e (Ideal.Quotient.mk (I.map (algebraMap R C)) c)) :=
      (Algebra.trace_eq_of_algEquiv e _).symm
    _ = (↑(Module.finrank A D) : A) := by
      rw [hsplit, Algebra.trace_prod_apply]
      change Algebra.trace A D (1 : D) + Algebra.trace A E (0 : E) = _
      rw [map_zero, add_zero, htrOne]

end SelectedJOneCRTTrace318

#print axioms SelectedJOneCRTTrace318.exists_selected_trace
