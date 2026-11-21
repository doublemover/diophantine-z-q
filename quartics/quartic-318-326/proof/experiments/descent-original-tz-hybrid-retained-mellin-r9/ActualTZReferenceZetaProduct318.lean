module
public import ActualTZFiniteMovingReference318
public section
noncomputable section
namespace ActualTZReferenceZetaProduct318
open Filter
open scoped BigOperators Topology
open ActualTZFiniteMovingReference318 ActualTZReferenceFactorNearOne318
open ActualTZRegulatedZetaAlgebra318

variable {I : Type*} [Fintype I]

@[expose] def partial (s t : I→ℂ) (P : ℕ) : ℂ :=
  ∏ p∈Nat.primesBelow P,∏ i : I,B p (s i) (t i)

@[expose] def zetaRatio (s t : I→ℂ) : ℂ :=
  ∏ i : I,riemannZeta (1+(s i+t i))/(riemannZeta (1+s i)*riemannZeta (1+t i))

private def factor (p : ℕ) (s : ℂ) : ℂ :=
  (1-(p:ℂ)^(-(1+s)))⁻¹

private theorem translate (p : ℕ) (hp : p.Prime) (s : ℂ) :
    (p:ℂ)^(-(1+s))=(1/(p:ℂ))*(p:ℂ)^(-s) := by
  have hp₀ : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  rw [neg_add,Complex.cpow_add _ _ hp₀,Complex.cpow_neg_one,one_div]

private theorem factor_eq (p : ℕ) (hp : p.Prime) (s t : ℂ) :
    B p s t=factor p (s+t)/(factor p s*factor p t) := by
  have hp₀ : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  simp only [B,oneSite,factor,translate p hp,neg_add s t,Complex.cpow_add _ _ hp₀,
    div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] <;> ac_rfl

private theorem euler (s : ℂ) (hs : 0<s.re) :
    Tendsto (fun P : ℕ => ∏ p∈Nat.primesBelow P,factor p s)
      atTop (𝓝 (riemannZeta (1+s))) := by
  have H : 1<((1:ℂ)+s).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  exact riemannZeta_eulerProduct H

private theorem one_row (s t : ℂ) (hs : 0<s.re) (ht : 0<t.re) :
    Tendsto (fun P : ℕ => ∏ p∈Nat.primesBelow P,B p s t)
      atTop (𝓝 (riemannZeta (1+(s+t))/(riemannZeta (1+s)*riemannZeta (1+t)))) := by
  have nz (v : ℂ) (hv : 0<v.re) : riemannZeta (1+v)≠0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hst : 0<(s+t).re := by simp only [Complex.add_re]; linarith
  have H := (euler (s+t) hst).div ((euler s hs).mul (euler t ht))
    (mul_ne_zero (nz s hs) (nz t ht))
  refine H.congr' (Eventually.of_forall fun P => ?_)
  symm
  calc
    _ = ∏ p∈Nat.primesBelow P,factor p (s+t)/(factor p s*factor p t) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact factor_eq p (Nat.prime_of_mem_primesBelow hp) s t
    _ = _ := by rw [Finset.prod_div_distrib,Finset.prod_mul_distrib]

theorem partial_tendsto (s t : I→ℂ) (hs : ∀ i,0<(s i).re) (ht : ∀ i,0<(t i).re) :
    Tendsto (partial s t) atTop (𝓝 (zetaRatio s t)) := by
  unfold zetaRatio
  have H := tendsto_finsetProd (Finset.univ : Finset I) (fun i _ => one_row (s i) (t i) (hs i) (ht i))
  refine H.congr' (Eventually.of_forall fun P => ?_)
  exact Finset.prod_comm

/-- Full ζ-quotient compared to its literal P=N+1 truncation.
No inverse ζ bound at high imaginary height is used, and the factor
‖partial‖ appears multiplicatively, even if an arbitrary phase is
considered. -/
theorem omitted_relative (L : ℝ) (hL : 0<L) (N : ℕ)
    (hN : Real.exp (L^2)≤(N:ℝ)) (s t : I→ℂ)
    (hs : ∀ i,1/L≤(s i).re) (ht : ∀ i,1/L≤(t i).re) :
    ‖zetaRatio s t-partial s t (N+1)‖ ≤ ‖partial s t (N+1)‖*
      (Real.exp (7*(Fintype.card I:ℝ)*(L*Real.exp (-L)))-1) := by
  have hσ : (0:ℝ)<1/L := by positivity
  have H := partial_tendsto s t (fun i => hσ.trans_le (hs i)) (fun i => hσ.trans_le (ht i))
  have hLim := (continuous_norm.tendsto (zetaRatio s t-partial s t (N+1))).comp
    (H.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => partial s t (N+1))
      atTop (𝓝 (partial s t (N+1)))))
  apply le_of_tendsto hLim
  refine eventually_atTop.mpr ⟨N+1,fun P hP => ?_⟩
  have hCut : (Nat.primesBelow P).filter (fun p => p≤N)=Nat.primesBelow (N+1) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_,hp⟩,h⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨⟨h.trans_le hP,hp⟩,by omega⟩
  let T : ℂ := ∏ p∈(Nat.primesBelow P).filter (fun p => N<p),∏ i : I,B p (s i) (t i)
  have hSplit : partial s t P=partial s t (N+1)*T := by
    unfold partial
    simpa only [T,not_le,hCut] using (Finset.prod_filter_mul_prod_filter_not
      (Nat.primesBelow P) (fun p => p≤N) (fun p => ∏ i : I,B p (s i) (t i))).symm
  change ‖partial s t P-partial s t (N+1)‖≤_
  have hE : partial s t (N+1)*T-partial s t (N+1)=
      partial s t (N+1)*(T-1) := by ring
  rw [hSplit,hE,norm_mul]
  exact mul_le_mul_of_nonneg_left (omitted_finite_tail L hL N hN P s t hs ht) (norm_nonneg _)

/-- The tail coefficient converges to zero for the exact growth
choice N≥exp(L²). The cutoff itself was never taken to infinity at a
fixed regulator and then reused at a moving one. -/
theorem relative_error_tendsto (k : ℕ) :
    Tendsto (fun L : ℝ=>Real.exp (7*(k:ℝ)*(L*Real.exp (-L)))-1)
      atTop (𝓝 0) := by
  have A : Tendsto (fun L : ℝ=>L*Real.exp (-L)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have H : Tendsto (fun L : ℝ=>7*(k:ℝ)*(L*Real.exp (-L))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ=>7*(k:ℝ)) atTop (𝓝 (7*(k:ℝ)))).mul A
  have h := ((Real.continuous_exp.tendsto 0).comp H).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(1:ℝ)) atTop (𝓝 1))
  simpa only [Real.exp_zero,sub_self,Function.comp_def] using h

end ActualTZReferenceZetaProduct318
