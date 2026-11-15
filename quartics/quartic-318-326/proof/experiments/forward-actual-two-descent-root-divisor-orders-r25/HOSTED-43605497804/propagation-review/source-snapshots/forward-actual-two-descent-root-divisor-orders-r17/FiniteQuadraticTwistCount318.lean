module
public import FiniteCurveCharacterCount318
public section
noncomputable section
namespace FiniteQuadraticTwistCount318
open FiniteCurveCharacterCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def scaleEquiv (c : F) (hc : c≠0) : F ≃ F where
  toFun x := c*x
  invFun x := c⁻¹*x
  left_inv x := by simp only [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
  right_inv x := by simp only [←mul_assoc,mul_inv_cancel₀ hc,one_mul]

/-- The actual coordinate change x↦cx gives the opposite quadratic
character sum whenever c is a nonsquare. -/
theorem sum_twist (D c : F) (hc : c≠0) (hchar : quadraticChar F c= -1) :
    traceSum (D*c^2)= -traceSum D := by
  classical
  calc
    traceSum (D*c^2)=∑ x : F, quadraticChar F ((c*x)^3-(D*c^2)*(c*x)) :=
      (Equiv.sum_comp (scaleEquiv c hc) (fun x : F => quadraticChar F (x^3-(D*c^2)*x))).symm
    _ = ∑ x : F, -quadraticChar F (x^3-D*x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (c*x)^3-(D*c^2)*(c*x)=c^3*(x^3-D*x) by ring,map_mul,map_pow,hchar]
      ring
    _ = -traceSum D := by rw [Finset.sum_neg_distrib] <;> rfl

theorem count_twist (hF : ringChar F≠2) (D c : F) (hc : c≠0)
    (hchar : quadraticChar F c= -1) : count D+count (D*c^2)=2*(Fintype.card F+1) := by
  have h₁ := count_formula hF D
  have h₂ := count_formula hF (D*c^2)
  rw [sum_twist D c hc hchar] at h₂
  have he : (count D:ℤ)+(count (D*c^2):ℤ)=2*((Fintype.card F:ℤ)+1) := by linarith
  exact_mod_cast he

/-- The two literal coefficients (3−rho)² and (3+rho)² are opposite
quadratic twists when the product7 has character−1. -/
theorem conjugate_counts (hF : ringChar F≠2) (rho : F) (hr : rho^2=2)
    (hseven : quadraticChar F (7:F)= -1) :
    count ((3-rho)^2)+count ((3+rho)^2)=2*(Fintype.card F+1) := by
  have h7 : (7:F)≠0 := by intro hz; rw [hz,map_zero] at hseven; norm_num at hseven
  have hprod : (3-rho)*(3+rho)=7 := by linear_combination -hr
  have hm : 3-rho≠0 := by intro hz; rw [hz,zero_mul] at hprod; exact h7 hprod.symm
  have hp : 3+rho≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact h7 hprod.symm
  let c := (3+rho)/(3-rho)
  have hc : c≠0 := div_ne_zero hp hm
  have he : c*(3-rho)^2=7 := by
    calc
      c*(3-rho)^2=(3-rho)*(3+rho) := by dsimp [c]; field_simp [hm] <;> ring
      _ = 7 := hprod
  have hchar : quadraticChar F c= -1 := by
    have hh := congrArg (quadraticChar F) he
    rw [map_mul,quadraticChar_sq_one' hm,mul_one,hseven] at hh
    exact hh
  have hcoeff : (3-rho)^2*c^2=(3+rho)^2 := by dsimp [c]; field_simp [hm] <;> ring
  simpa only [hcoeff] using count_twist hF ((3-rho)^2) c hc hchar

end FiniteQuadraticTwistCount318
