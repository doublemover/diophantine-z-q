module
public import ActualTZCollisionPrimePartition318
public section
noncomputable section
namespace ActualTZActualCollisionAverage318
open scoped BigOperators
open ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
attribute [local instance] Classical.propDecidable

variable {I Z R : Type*} [Fintype I] [DecidableEq I] [Fintype Z] [Fintype R]

/-- Typed accepting cup for the true original wrap weights. It
uses only sparse per-prime marginals for actual literal differences,
nonzero-cell horizon, and total retained weight at most 1.
Exact zeros of θ are skipped before using arithmetic hypotheses. -/
theorem corrected_average (W P y N K : ℕ) (a : Z→R→I→ℤ) (b : Z→R→I→ℕ)
    (m : Z→ℝ) (θ : Z→R→ℝ) (σ : ℝ) (hσ : 0<σ)
    (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re)
    (hW : ∀ p,p.Prime→p≤y→p∣W)
    (hm : ∀ z,0≤m z) (hθ : ∀ z r,0≤θ z r)
    (hTotal : (∑ z : Z,m z*(∑ r : R,θ z r))≤1)
    (hU : ∀ z r,0<θ z r→∀ i,W.Coprime (b z r i))
    (hHorizon : ∀ z r,0<θ z r→∀ p∈offWheel W P,
      hit W p (a z r) (b z r)→p≤2*N)
    (M C : ℝ) (hM : 0<M)
    (hMarginal : ∀ p∈regular y N K,
      (∑ z : Z,m z*(∑ r : R,θ z r*
        (if hit W p (a z r) (b z r) then 1 else 0)))≤C*(1/(p:ℝ)+1/M)) :
    let G := goodConst (Fintype.card I)*(∑ p∈offWheel W P,(1/(p:ℝ))^2)+
      badConst (Fintype.card I)*extra W P K
    (∑ z : Z,m z*(∑ r : R,θ z r*
      ‖corrected W P (a z r) (b z r) s t-1‖)) ≤
    (Real.exp G-1)+Real.exp G*(∑ p∈regular y N K,
      prefixWeight (badConst (Fintype.card I)) p*(C*(1/(p:ℝ)+1/M))) := by
  intro G
  let B := badConst (Fintype.card I)
  let h (z : Z) (r : R) (p : ℕ) := hit W p (a z r) (b z r)
  let err (z : Z) (r : R) : ℝ :=
    Real.exp (B*(∑ p∈regular y N K,reciprocalHit (h z r) p))-1
  have hB : 0≤B := bad_nonnegative _
  have hG : 0≤G := by
    dsimp only [G]
    exact add_nonneg (mul_nonneg (good_nonnegative _) (Finset.sum_nonneg fun _ _=>sq_nonneg _))
      (mul_nonneg hB (extra_nonneg W P K))
  have hG' : 0≤Real.exp G-1 := sub_nonneg.mpr
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hG)
  have hP (z : Z) (r : R) (hz : 0<θ z r) :
      ‖corrected W P (a z r) (b z r) s t-1‖≤
        (Real.exp G-1)+Real.exp G*err z r := by
    have H := corrected_error W P (a z r) (b z r) (hU z r hz) σ hσ s t hs ht
    have hS := split W P y N K (h z r) hW (hHorizon z r hz)
    refine H.trans ?_
    calc
      _ ≤ Real.exp (G+B*(∑ p∈regular y N K,reciprocalHit (h z r) p))-1 := by
        apply sub_le_sub_right
        apply Real.exp_le_exp.mpr
        have hCross := mul_le_mul_of_nonneg_left hS hB
        have hD := add_le_add_left hCross
          (goodConst (Fintype.card I)*(∑ p∈offWheel W P,(1/(p:ℝ))^2))
        simpa only [G,B,h,mul_add,add_assoc] using hD
      _ = _ := by dsimp only [err]; rw [Real.exp_add]; ring
  have hAvg := wrap_average (regular y N K) (regular_prime y N K)
    m θ h B hB (fun p=>C*(1/(p:ℝ)+1/M)) hm hθ hMarginal
  calc
    _ ≤ ∑ z : Z,m z*(∑ r : R,θ z r*((Real.exp G-1)+Real.exp G*err z r)) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (hm z)
      apply Finset.sum_le_sum
      intro r _
      by_cases H : θ z r=0
      · simp only [H,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hP z r (lt_of_le_of_ne (hθ z r) H.symm)) (hθ z r)
    _ = (Real.exp G-1)*(∑ z : Z,m z*(∑ r : R,θ z r))+
        Real.exp G*(∑ z : Z,m z*(∑ r : R,θ z r*err z r)) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      all_goals
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_left hTotal hG').trans_eq (mul_one _))
      (mul_le_mul_of_nonneg_left hAvg (Real.exp_pos G).le)

end ActualTZActualCollisionAverage318
