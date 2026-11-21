module
public import Mathlib
public section
noncomputable section
namespace ActualTZThreeNearFactors318
open scoped BigOperators

private theorem reverse_upper (A B : ℂ) : ‖A‖≤‖B‖+‖B-A‖ := by
  have h : A=B-(B-A) := by ring
  nth_rw 1 [h]
  exact norm_sub_le _ _

@[expose] def drift (ε τ ω : ℝ) : ℝ :=
  let d := ε+2*τ*(1+ε)
  d+ω*(1+d)

theorem drift_nonneg (ε τ ω : ℝ) (he : 0≤ε) (ht : 0≤τ) (hw : 0≤ω) :
    0≤drift ε τ ω := by simp only [drift]; positivity

/-- Uniform relative comparison WITHOUT dividing by the main
kernel. The omitted-prime comparison is relative to the partial
product, not (silently) to the full one. -/
theorem near_reference (P Z K M : ℂ) (ε τ ω : ℝ)
    (he : 0≤ε) (ht : 0≤τ) (ht' : τ≤1/2) (hw : 0≤ω)
    (hP : ‖Z-P‖≤‖P‖*τ) (hZ : ‖Z-K‖≤‖K‖*ε) (hM : ‖M-1‖≤ω) :
    ‖M*P-K‖≤‖K‖*drift ε τ ω := by
  let d := ε+2*τ*(1+ε)
  have hZ' : ‖Z‖≤‖K‖*(1+ε) := by
    have H := reverse_upper Z K
    rw [norm_sub_rev K Z] at H
    linarith only [H,hZ]
  have hP₂ : ‖P‖≤2*‖Z‖ := by
    have H := reverse_upper P Z
    have H₂ := mul_le_mul_of_nonneg_left ht' (norm_nonneg P)
    linarith only [H,hP,H₂]
  have hP' : ‖P-K‖≤‖K‖*d := by
    have hEq : P-K=(P-Z)+(Z-K) := by ring
    have hTr := norm_add_le (P-Z) (Z-K)
    rw [←hEq,norm_sub_rev P Z] at hTr
    have hMul := mul_le_mul_of_nonneg_right
      (hP₂.trans (mul_le_mul_of_nonneg_left hZ' (by positivity))) ht
    dsimp only [d]
    nlinarith only [hTr,hP,hZ,hMul]
  have hPk : ‖P‖≤‖K‖*(1+d) := by
    have H := reverse_upper P K
    rw [norm_sub_rev K P] at H
    linarith only [H,hP']
  have hEq : M*P-K=(M-1)*P+(P-K) := by ring
  have h := norm_add_le ((M-1)*P) (P-K)
  rw [←hEq,norm_mul] at h
  have E := mul_le_mul hM hPk (norm_nonneg P) hw
  simp only [drift]
  change _ ≤ ‖K‖*(d+ω*(1+d))
  nlinarith only [h,E,hP']

/-- One pointwise row error after the reference/normalization are
fixed; no assumption that the collision factor is individually small. -/
theorem cell_near (B C K : ℂ) (η : ℝ) (h : ‖B-K‖≤‖K‖*η) :
    ‖B*C-K‖≤‖K‖*(η+(1+η)*‖C-1‖) := by
  have hB : ‖B‖≤‖K‖*(1+η) := by
    have H := reverse_upper B K
    rw [norm_sub_rev K B] at H
    linarith only [H,h]
  have he : B*C-K=B*(C-1)+(B-K) := by ring
  have hTr := norm_add_le (B*(C-1)) (B-K)
  rw [←he,norm_mul] at hTr
  have H := mul_le_mul_of_nonneg_right hB (norm_nonneg (C-1))
  nlinarith only [h,hTr,H]

/-- Finite actual average with shared kernel and arbitrary correlated
signed correction factors. Only a nonnegative weighted norm bound
is used, not independence or pointwise smallness. -/
theorem average_cell_near {J : Type*} [Fintype J] (w : J→ℝ)
    (h₀ : ∀ j,0≤w j) (h₁ : (∑ j : J,w j)≤1)
    (B K : ℂ) (c : J→ℂ) (η E : ℝ) (hη : 0≤η)
    (hB : ‖B-K‖≤‖K‖*η)
    (hC : (∑ j : J,w j*‖c j-1‖)≤E) :
    (∑ j : J,w j*‖B*c j-K‖)≤‖K‖*(η+(1+η)*E) := by
  calc
    _ ≤ ∑ j : J,w j*(‖K‖*(η+(1+η)*‖c j-1‖)) :=
      Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (cell_near B (c j) K η hB) (h₀ j)
    _ = ‖K‖*(η*(∑ j : J,w j)+(1+η)*(∑ j : J,w j*‖c j-1‖)) := by
      rw [Finset.mul_sum _ _ η,Finset.mul_sum _ _ (1+η),←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have A := mul_le_mul_of_nonneg_left h₁ hη
      have B := mul_le_mul_of_nonneg_left hC (by linarith : 0≤1+η)
      linarith only [A,B]

end ActualTZThreeNearFactors318
