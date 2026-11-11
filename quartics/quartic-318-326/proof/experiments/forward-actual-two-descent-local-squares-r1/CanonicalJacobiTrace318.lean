module
public import CanonicalCMNormBridge318
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public section
noncomputable section
namespace CanonicalJacobiTrace318
open FiniteCurveCharacterCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def squareFibers : F ≃ (Σ t : F, {x : F // x^2=t}) where
  toFun x := ⟨x^2,x,rfl⟩
  invFun z := z.2.1
  left_inv x := rfl
  right_inv z := by rcases z with ⟨t,x,hx⟩; cases hx; rfl

/-- Weighted counting of all square fibers, including the zero fiber. -/
theorem weighted_squares (hF : ringChar F≠2) (g : F → ℂ) :
    (∑ x : F, g (x^2))=∑ t : F, ((quadraticChar F t:ℂ)+1)*g t := by
  classical
  calc
    _ = ∑ z : (Σ t : F, {x : F // x^2=t}), g z.1 :=
      (Equiv.sum_comp squareFibers (fun z => g z.1)).symm
    _ = ∑ t : F, (Fintype.card {x : F // x^2=t}:ℂ)*g t := by
      simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have hc : (Fintype.card {x : F // x^2=t}:ℂ)=(quadraticChar F t:ℂ)+1 := by
        have h := FiniteCurveCharacterCount318.fiber_count hF t
        rw [Nat.card_eq_fintype_card] at h
        exact_mod_cast h
      rw [hc]

@[expose] def quadraticComplex : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

lemma quadraticComplex_apply (x : F) : quadraticComplex x=(quadraticChar F x:ℂ) := rfl

/-- The actual canonical cubic character sum is the sum of two conjugate
quartic Jacobi sums. The quartic character is not yet produced here. -/
theorem trace_jacobi (hF : ringChar F≠2)
    (hminus : quadraticChar F (-1:F)=1) (ψ : MulChar F ℂ)
    (hsq : ψ^2=quadraticComplex) (hfour : ψ^4=1) :
    (traceSum (1:F):ℂ)=jacobiSum ψ quadraticComplex+
      jacobiSum ψ⁻¹ quadraticComplex := by
  have hi : ψ^3=ψ⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa only [←pow_succ] using hfour
  have hinv (t : F) : ψ⁻¹ t=ψ t*quadraticComplex t := by
    have he : ψ⁻¹=ψ*quadraticComplex := by rw [←hi,←hsq]; group
    rw [he,MulChar.mul_apply]
  have hsquare (x : F) : ψ (x^2)=quadraticComplex x := by
    have h := congrArg (fun χ : MulChar F ℂ => χ x) hsq
    simpa only [pow_two,MulChar.mul_apply,map_mul] using h
  have hcubic (x : F) :
      ψ (x^2)*quadraticComplex (1-x^2)=(quadraticChar F (x^3-x):ℂ) := by
    rw [hsquare,←map_mul]
    rw [show x*(1-x^2)=(-1:F)*(x^3-x) by ring,map_mul]
    have hm : quadraticComplex (-1:F)=1 := by
      rw [quadraticComplex_apply,hminus]; norm_num
    rw [hm,one_mul,quadraticComplex_apply]
  have hw := weighted_squares hF (fun t : F => ψ t*quadraticComplex (1-t))
  have hl : (∑ x : F, ψ (x^2)*quadraticComplex (1-x^2))=(traceSum (1:F):ℂ) := by
    simp_rw [hcubic]
    simp only [traceSum,one_mul,Int.cast_sum]
  rw [hl] at hw
  rw [hw]
  rw [jacobiSum,jacobiSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hinv,quadraticComplex_apply]
  ring

end CanonicalJacobiTrace318
