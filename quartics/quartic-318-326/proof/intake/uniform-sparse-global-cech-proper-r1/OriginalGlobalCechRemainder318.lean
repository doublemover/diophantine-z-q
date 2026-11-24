module
public import OriginalSexticRemainderCanonical318
public section
noncomputable section
namespace OriginalGlobalCechRemainder318
open Polynomial OriginalSexticJetMarked318 OriginalSexticJetResidues318
variable {E K : Type*} [Field E] [Field K] [Algebra E K]

/-- Both the exact degree and the scale of the defining equation are determined
by the fixed labelled factorization, without a monicity assumption. -/
theorem sextic (J : Certificate E K) : J.F.natDegree=6 ∧ J.F.leadingCoeff=J.a := by
  let σ:=algebraMap E K
  have hn : (algebraMap E K) J.a ≠ 0 := (map_ne_zero_iff σ σ.injective).2 J.leading_nonzero
  have e:=J.factorization
  constructor
  · have h:=congrArg Polynomial.natDegree e
    simp only [natDegree_map,split,natDegree_C_mul hn,natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero (J.labels i)),
      natDegree_X_sub_C,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
    exact h.trans (by decide)
  · apply σ.injective
    have h:=congrArg Polynomial.leadingCoeff e
    simpa only [leadingCoeff_map,split,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_prod,
      leadingCoeff_X_sub_C,Finset.prod_const_one,mul_one] using h

@[expose] def coef (J : Certificate E K) (i : Fin 3) : E := (J.remainder i).coeff 5 / J.a

@[expose] def step (J : Certificate E K) (i : Fin 3) : E[X] := X*J.remainder i-C (coef J i)*J.F

theorem small_step (J : Certificate E K) (i : Fin 3) : (step J i).natDegree≤5 := by
  obtain ⟨hf,ha⟩:=sextic J
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [step,coeff_sub,coeff_X_mul,coeff_C_mul]
  by_cases he : n=5
  · subst n
    have hc : J.F.coeff 6=J.a := by rw [←hf,coeff_natDegree,ha]
    rw [show Nat.succ 5=6 by rfl,hc,coef,div_mul_cancel₀ _ J.leading_nonzero,sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt (by have:=J.small i; omega : (J.remainder i).natDegree<n),
        coeff_eq_zero_of_natDegree_lt (by omega : J.F.natDegree < n+1), mul_zero,sub_self]

theorem next (J : Certificate E K) (i j : Fin 3) (hij : (j:ℕ)=(i:ℕ)+1) :
    step J i = J.remainder j := by
  obtain ⟨q,hq⟩:=J.relation i
  refine OriginalSexticRemainderCanonical318.unique_remainder J j (step J i)
    (X*q+C (coef J i)*J.F.derivative) (small_step J i) ?_
  rw [hij,pow_succ,step]
  calc
    _ = X*(X^(i:ℕ)*J.G-J.remainder i*J.F.derivative)+J.F*(C (coef J i)*J.F.derivative) := by ring
    _ = _ := by rw [hq]; ring

@[expose] def A (J : Certificate E K) : E[X] := C (coef J 0)*X^2+C (coef J 1)*X+C (coef J 2)
@[expose] def P (J : Certificate E K) : E[X] := step J 2

theorem P_eq (J : Certificate E K) : P J = X^3*J.remainder 0-J.F*A J := by
  have h0:= next J 0 1 rfl
  have h1:= next J 1 2 rfl
  unfold P step at *
  rw [←h1,←h0]
  unfold A
  ring

theorem reciprocal_derivative_small (F : E[X]) (hf : F.natDegree≤6) :
    (C (6:E)*F-X*F.derivative).natDegree≤5 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [coeff_sub,coeff_C_mul,coeff_X_mul,coeff_derivative]
  by_cases he : n=5
  · subst n; norm_num; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : F.natDegree< n+1), mul_zero,zero_mul,sub_self]

@[expose] def Qstar (J : Certificate E K) (q : E[X]) : E[X] :=
  X^4*q+X*J.F.derivative*A J+C 6*P J

theorem Qstar_eq (J : Certificate E K) (q : E[X]) (hq : J.G-J.remainder 0*J.F.derivative=J.F*q) :
    J.F*Qstar J q = X^4*J.G+(C 6*J.F-X*J.F.derivative)*P J := by
  have e : J.G=J.F*q+J.remainder 0*J.F.derivative := (sub_eq_iff_eq_add).mp hq
  rw [e,Qstar,P_eq]; ring

theorem Qstar_small (J : Certificate E K) (q : E[X]) (hq : J.G-J.remainder 0*J.F.derivative=J.F*q) :
    (Qstar J q).natDegree≤4 := by
  by_cases hz : Qstar J q=0
  · rw [hz,natDegree_zero]; decide
  obtain ⟨hf,_⟩:=sextic J
  have nf : J.F≠0 := fun h => by simp [h] at hf
  have h2 := reciprocal_derivative_small J.F hf.le
  have h3 : (P J).natDegree ≤ 5 := small_step J 2
  have h4 : ((X:E[X])^4*J.G).natDegree ≤ 10 :=
    (natDegree_mul_le ..).trans (by rw [natDegree_X_pow]; have:=J.true_jet_degree; omega)
  have h5 : ((C 6*J.F-X*J.F.derivative)*P J).natDegree ≤ 10 :=
    (natDegree_mul_le ..).trans (by omega)
  have h : (J.F*Qstar J q).natDegree ≤ 10 := by
    rw [Qstar_eq J q hq]; exact (natDegree_add_le ..).trans (max_le h4 h5)
  rw [natDegree_mul nf hz,hf] at h
  omega

end OriginalGlobalCechRemainder318
#print axioms OriginalGlobalCechRemainder318.P_eq
#print axioms OriginalGlobalCechRemainder318.Qstar_small
