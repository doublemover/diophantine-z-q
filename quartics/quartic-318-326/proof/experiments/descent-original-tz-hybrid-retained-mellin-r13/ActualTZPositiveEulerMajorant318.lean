module
public import Mathlib
public section
noncomputable section
namespace ActualTZPositiveEulerMajorant318
open Filter MeasureTheory Set
open scoped BigOperators Topology

@[expose] def q (σ : ℝ) (p : ℕ) : ℝ := (p:ℝ)^(-1-σ)

theorem q_bounds (σ : ℝ) (hσ : 0<σ) {p : ℕ} (hp : p.Prime) :
    0≤q σ p ∧ q σ p<1 := by
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_lt_one_of_one_lt_of_neg hp' (by linarith)⟩

private theorem one_add_nat_le_pow (r : ℝ) (hr : 0≤r) (D : ℕ) :
    1+(D:ℝ)*r ≤ (1+r)^D := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Nat.cast_succ,pow_succ]
      calc
        _ ≤ (1+(D:ℝ)*r)*(1+r) := by nlinarith [mul_nonneg (Nat.cast_nonneg D) (sq_nonneg r)]
        _ ≤ _ := mul_le_mul_of_nonneg_right ih (by positivity)

private theorem atom_le (r : ℝ) (hr : 0≤r) (h₁ : r<1) (D : ℕ) :
    1+(D:ℝ)*r ≤ (((1-r)⁻¹:ℝ)^D) := by
  apply (one_add_nat_le_pow r hr D).trans
  apply pow_le_pow_left₀ (by positivity) _ _
  have hd : 0<1-r := sub_pos.mpr h₁
  rw [←one_div]
  apply (le_div_iff₀ hd).2
  nlinarith

/-- This is the positive baseline for the raw absolute assignment sum.
It is drawn from the exact pinned ζ Euler product, not from an
estimate for inverse ζ at large imaginary frequency. -/
theorem reference_tendsto (σ : ℝ) (hσ : 0<σ) :
    Tendsto (fun P : ℕ => ∏ p∈Nat.primesBelow P,(1-q σ p)⁻¹) atTop
      (𝓝 ‖riemannZeta ((1+σ:ℝ):ℂ)‖) := by
  have hs : (1:ℝ)<(((1+σ:ℝ):ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have H := riemannZeta_eulerProduct (s := ((1+σ:ℝ):ℂ)) hs
  have K := (continuous_norm.tendsto (riemannZeta ((1+σ:ℝ):ℂ))).comp H
  refine K.congr' (Eventually.of_forall fun P => ?_)
  simp only [Function.comp_def,Complex.norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hr := (q_bounds σ hσ hp').2
  have he : (p:ℂ)^(-((1+σ:ℝ):ℂ)) = (q σ p:ℂ) := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_neg,←Complex.ofReal_cpow (by positivity)]
    congr 1
    unfold q
    congr 1
    ring
  rw [he,norm_inv,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_of_nonneg]
  exact sub_nonneg.mpr hr.le

theorem reference_upper (σ : ℝ) (hσ : 0<σ) (P : ℕ) :
    (∏ p∈Nat.primesBelow P,(1-q σ p)⁻¹)≤‖riemannZeta ((1+σ:ℝ):ℂ)‖ := by
  apply ge_of_tendsto (reference_tendsto σ hσ)
  apply eventually_atTop.mpr
  refine ⟨P,fun n hn => ?_⟩
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Nat.primesBelow_mono hn)
  · intro p hp
    have H := (q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)).2
    exact inv_nonneg.mpr (sub_nonneg.mpr H.le)
  · intro p hp _
    have H := q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)
    rw [←one_div,le_div_iff₀ (sub_pos.mpr H.2),one_mul]
    linarith [H.1]

/-- Uniform bound for any finite number of actual two-slot local
choices after its all-off term is separated. -/
theorem zeta_power (σ : ℝ) (hσ : 0<σ) (P D : ℕ) (A : ℕ→ℝ)
    (h₀ : ∀ p∈Nat.primesBelow P,0≤A p)
    (hA : ∀ p∈Nat.primesBelow P,A p≤1+(D:ℝ)*q σ p) :
    (∏ p∈Nat.primesBelow P,A p) ≤ ‖riemannZeta ((1+σ:ℝ):ℂ)‖^D := by
  calc
    _ ≤ ∏ p∈Nat.primesBelow P,((1-q σ p)⁻¹)^D := by
      apply Finset.prod_le_prod₀ h₀
      intro p hp
      have H := q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)
      exact (hA p hp).trans (atom_le _ H.1 H.2 D)
    _ = (∏ p∈Nat.primesBelow P,(1-q σ p)⁻¹)^D := by
      rw [Finset.prod_pow]
    _ ≤ _ := by
      apply pow_le_pow_left₀ _ (reference_upper σ hσ P)
      apply Finset.prod_nonneg
      intro p hp
      exact inv_nonneg.mpr (sub_nonneg.mpr (q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)).2.le)

/-- Integer p-series domination of any omitted prime tail. At
σ=1/L and N≥exp(L²), this is at most L*exp(-L). -/
theorem integer_tail (σ : ℝ) (hσ : 0<σ) (N : ℕ) (hN : 0<N) :
    (∑' n : ℕ,((n+N+1:ℕ):ℝ)^(-1-σ)) ≤ (N:ℝ)^(-σ)/σ := by
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN
  have hs : (-1:ℝ)-σ< -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x^(-1-σ)) (Set.Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have h := AntitoneOn.tsum_comp_add_le_integral N hanti
    (integrableOn_Ioi_rpow_of_lt hs hN') (fun x hx => Real.rpow_nonneg (by linarith only [hN',mem_Ioi.mp hx]) _)
  rw [integral_Ioi_rpow_of_lt hs hN',
    show (-1:ℝ)-σ+1= -σ by ring,div_neg,neg_neg] at h
  exact h

/-- A numerical moving-regulator bound for the positive reference
zeta, proved from the actual Dirichlet series and integral test. -/
theorem zeta_norm_upper (σ : ℝ) (hσ : 0<σ) :
    ‖riemannZeta ((1+σ:ℝ):ℂ)‖≤1+1/σ := by
  let f : ℕ→ℝ := fun n => ((n+1:ℕ):ℝ)^(-1-σ)
  have hs : (1:ℝ)<(((1+σ:ℝ):ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hsum : Summable f :=
    (Real.summable_nat_rpow.mpr (by linarith : (-1:ℝ)-σ< -1)).comp_injective Nat.succ_injective
  have hz : riemannZeta ((1+σ:ℝ):ℂ) = ((∑' n : ℕ,f n):ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs,Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [f,show (-1:ℝ)-σ=-(1+σ) by ring,Complex.ofReal_cpow (by positivity),
      Complex.ofReal_neg,Complex.cpow_neg,one_div]
    simp only [Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
  rw [hz,Complex.norm_of_nonneg (tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _)]
  rw [hsum.tsum_eq_zero_add]
  have h₀ : f 0=1 := by simp [f]
  rw [h₀]
  apply add_le_add_left
  simpa only [f,Nat.cast_one,Real.one_rpow,one_div] using integer_tail σ hσ 1 (by decide)

end ActualTZPositiveEulerMajorant318
