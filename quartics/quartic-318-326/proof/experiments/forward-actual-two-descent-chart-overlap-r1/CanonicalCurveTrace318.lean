module
public import FiniteQuadraticTwistCount318
public section
noncomputable section
namespace CanonicalCurveTrace318
open FiniteCurveCharacterCount318 FiniteQuadraticTwistCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Scaling the actual abscissa retains the quadratic character, not just
its nonsquare special case. This applies uniformly to every square coefficient. -/
theorem trace_scale (D c : F) (hc : c≠0) :
    traceSum (D*c^2)=quadraticChar F c*traceSum D := by
  classical
  have hs : (quadraticChar F c)^2=1 := by
    simpa only [map_pow] using (quadraticChar_sq_one' hc)
  have hcube : (quadraticChar F c)^3=quadraticChar F c := by
    calc
      (quadraticChar F c)^3=quadraticChar F c*(quadraticChar F c)^2 := by ring
      _ = quadraticChar F c := by rw [hs,mul_one]
  calc
    traceSum (D*c^2)=∑ x : F, quadraticChar F ((c*x)^3-(D*c^2)*(c*x)) :=
      (Equiv.sum_comp (scaleEquiv c hc)
        (fun x : F => quadraticChar F (x^3-(D*c^2)*x))).symm
    _ = ∑ x : F, quadraticChar F c*quadraticChar F (x^3-D*x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (c*x)^3-(D*c^2)*(c*x)=c^3*(x^3-D*x) by ring,
        map_mul,map_pow,hcube]
    _ = quadraticChar F c*traceSum D := by rw [Finset.mul_sum]; rfl

/-- The square of the literal Frobenius trace is independent of all root
choices and all nonzero square-coefficient twists. -/
theorem trace_square (c : F) (hc : c≠0) :
    (traceSum (c^2))^2=(traceSum (1:F))^2 := by
  have hs : (quadraticChar F c)^2=1 := by
    simpa only [map_pow] using (quadraticChar_sq_one' hc)
  have he := trace_scale (1:F) c hc
  simp only [one_mul] at he
  rw [he,mul_pow,hs,one_mul]

/-- The unsiged canonical trace equation suffices for the two exact
neighboring Gaussian counts. This does not presume a choice of Gaussian associate. -/
theorem count_neighbors (hF : ringChar F≠2) (c : F) (hc : c≠0)
    (a b : ℤ) (hnorm : (Fintype.card F:ℤ)=a^2+b^2)
    (hcm : (traceSum (1:F))^2=4*a^2) :
    count (c^2)=GaussianNeighborNorms318.minus a b ∨
    count (c^2)=GaussianNeighborNorms318.plus a b := by
  have hs : (traceSum (c^2))^2=4*a^2 := (trace_square c hc).trans hcm
  have hfactor : (traceSum (c^2)-2*a)*(traceSum (c^2)+2*a)=0 := by nlinarith
  have hcount := count_formula hF (c^2)
  have hm : (GaussianNeighborNorms318.minus a b:ℤ)=(a-1)^2+b^2 :=
    GaussianNeighborNorms318.norm_cast (a-1) b
  have hp : (GaussianNeighborNorms318.plus a b:ℤ)=(a+1)^2+b^2 :=
    GaussianNeighborNorms318.norm_cast (a+1) b
  rcases mul_eq_zero.mp hfactor with h|h
  · right
    have he : (count (c^2):ℤ)=(GaussianNeighborNorms318.plus a b:ℤ) := by nlinarith
    exact_mod_cast he
  · left
    have he : (count (c^2):ℤ)=(GaussianNeighborNorms318.minus a b:ℤ) := by nlinarith
    exact_mod_cast he

end CanonicalCurveTrace318
