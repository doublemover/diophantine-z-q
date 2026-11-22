module
public import Mathlib.NumberTheory.EulerProduct.Basic
public import LinearA4PrimeAnalyticBounds318
public section
noncomputable section
namespace LinearA4OrdinaryPrimeHarmonic318
open scoped BigOperators
open LinearA4PrimeAnalyticBounds318

/-! The finite Euler-product/harmonic comparison is adapted from the
project’s historical ActualOrdinaryEulerHarmonic318. It is separated from
that earlier quadratic-sieve dependency tree and provides the prime sum
with the coefficient-one log-log lower bound required by the affine forms. -/

@[expose] def ordinaryFull (N : ℕ) : ℝ := ∏p∈Nat.primesBelow N,(1-1/(p:ℝ))⁻¹
lemma prime_reciprocal_series (p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => ((p^e:ℕ):ℝ)⁻¹) ((1-1/(p:ℝ))⁻¹) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hlt : 1/(p:ℝ)<1 := by
    apply (div_lt_iff₀ hp0).mpr
    simpa only [one_mul] using hp1
  have hh := hasSum_geometric_of_lt_one (by positivity : (0:ℝ)≤1/(p:ℝ)) hlt
  simpa only [Nat.cast_pow,inv_pow,one_div] using hh
lemma prime_reciprocal_norm_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖((p^e:ℕ):ℝ)⁻¹‖) := by
  have hh := (prime_reciprocal_series p hp).summable
  have he (e : ℕ) : ‖((p^e:ℕ):ℝ)⁻¹‖=((p^e:ℕ):ℝ)⁻¹ := by
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  simpa only [he] using hh

/-- A finite-prime geometric Euler sum at exponent1. Global harmonic
summability is NOT used: only each individual prime-power series is summable. -/
lemma actual_finite_reciprocal_euler (N : ℕ) :
    HasSum (fun n : Nat.factoredNumbers (Finset.range N) => (n.1:ℝ)⁻¹) (ordinaryFull N) := by
  have h1 : ((1:ℕ):ℝ)⁻¹=1 := by norm_num
  have hmul : ∀ {m n : ℕ},Nat.Coprime m n →
      ((m*n:ℕ):ℝ)⁻¹=(m:ℝ)⁻¹*(n:ℝ)⁻¹ := by
    intro m n _
    rw [Nat.cast_mul,mul_inv]
  have hprod :
      (∏ p ∈ (Finset.range N).filter Nat.Prime, ∑' e : ℕ, ((p^e:ℕ):ℝ)⁻¹) =
        ordinaryFull N := by
    unfold ordinaryFull
    apply Finset.prod_congr rfl
    intro p hp
    exact (prime_reciprocal_series p (Finset.mem_filter.mp hp).2).tsum_eq
  rw [← hprod]
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n:ℝ)⁻¹)
    h1 hmul prime_reciprocal_norm_summable (Finset.range N)).2

lemma actual_harmonic_le_euler (N : ℕ) :
    (∑n∈Finset.Ico 1 N,(n:ℝ)⁻¹)≤ordinaryFull N := by
  classical
  let f : ↥(Finset.Ico 1 N) → Nat.factoredNumbers (Finset.range N) := fun n =>
    ⟨n.1,Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by have hh := Finset.mem_Ico.mp n.2;omega,
      fun p hpn _ _ => Finset.mem_range.mpr (hpn.trans_lt (Finset.mem_Ico.mp n.2).2)⟩⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun n : Nat.factoredNumbers (Finset.range N) => n.1) h)
  have hh := hasSum_le_inj f hf (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.1))
    (fun _ => le_rfl)
    (hasSum_fintype (fun n : ↥(Finset.Ico 1 N) => (n.1:ℝ)⁻¹))
    (actual_finite_reciprocal_euler N)
  rw [← Finset.sum_coe_sort (Finset.Ico 1 N) (fun n : ℕ => (n:ℝ)⁻¹)]
  exact hh

lemma log_succ_harmonic (K : ℕ) :
    Real.log ((K:ℝ)+1)≤∑n∈Finset.range K,((n:ℝ)+1)⁻¹ := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hx : 0<(K:ℝ)+1 := by positivity
    have hy : 0<((K:ℝ)+1)+1 := by positivity
    have hl := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hl
    have he : (((K:ℝ)+1)+1)/((K:ℝ)+1)-1=((K:ℝ)+1)⁻¹ := by
      field_simp [hx.ne']
      ring
    rw [he] at hl
    rw [Finset.sum_range_succ,Nat.cast_succ]
    linarith

/-- Genuine logarithmic lower growth of the actual ordinary finite
prime Euler product, via the original integer harmonic sum. -/
theorem actual_ordinary_log_lower (N : ℕ) (hN : 1≤N) : Real.log (N:ℝ)≤ordinaryFull N := by
  obtain ⟨K,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  have he : (∑n∈Finset.range K,((n:ℝ)+1)⁻¹)=∑n∈Finset.Ico 1 (K+1),(n:ℝ)⁻¹ := by
    apply Finset.sum_bij (fun n _ => n+1)
    · intro n hn
      exact Finset.mem_Ico.mpr ⟨by omega,by have hh := Finset.mem_range.mp hn;omega⟩
    · intro n _ k _ hn
      omega
    · intro n hn
      have hh := Finset.mem_Ico.mp hn
      refine ⟨n-1,Finset.mem_range.mpr (by omega),by omega⟩
    · intro n _
      simp only [Nat.cast_add,Nat.cast_one]
  have hh := log_succ_harmonic K
  rw [he] at hh
  have ht := hh.trans (actual_harmonic_le_euler (K+1))
  simpa only [Nat.cast_succ] using ht

/-- One uniform Taylor remainder is sufficient; the exact coefficient one
in front of x matters for logarithmic sieve dimension. -/
theorem log_inverse_comparison (x : ℝ) (_hx : 0≤x) (hhalf : x≤1/2) :
    Real.log ((1-x)⁻¹) ≤ x+2*x^2 := by
  have h : 0<1-x := by linarith
  have one : (1-x)⁻¹-1=x/(1-x) := by
    field_simp [h.ne']
    ring
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
  rw [one] at hl
  apply hl.trans
  apply (div_le_iff₀ h).2
  nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1-2*x by linarith)]

theorem loglog_le_full (n : ℕ) (hn : 2≤n) :
    Real.log (Real.log (n:ℝ)) ≤
      (∑ p ∈ Nat.primesLE n,1/(p:ℝ)) + 2*squareBudget := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hpos := Real.log_pos hn'
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<n)
    (show (n:ℝ)<((n+1:ℕ):ℝ) by exact_mod_cast Nat.lt_succ_self n).le
  have hbase := hlog.trans (actual_ordinary_log_lower (n+1) (by omega))
  have hpord : 0<ordinaryFull (n+1) := hpos.trans_le hbase
  have h := (Real.log_le_log_iff hpos hpord).mpr hbase
  change Real.log (Real.log (n:ℝ)) ≤
    Real.log (∏ p ∈ Nat.primesLE n,(1-1/(p:ℝ))⁻¹) at h
  have hpHalf {p : ℕ} (hp : p ∈ Nat.primesLE n) : 1/(p:ℝ)≤1/2 := by
    have hpp : (2:ℝ)≤p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact one_div_le_one_div_of_le (by norm_num) hpp
  have hp0 {p : ℕ} (hp : p ∈ Nat.primesLE n) : 0<1-1/(p:ℝ) := by
    linarith [hpHalf hp]
  rw [Real.log_prod (fun p hp => inv_ne_zero (hp0 hp).ne')] at h
  apply h.trans
  calc
    _ ≤ ∑ p ∈ Nat.primesLE n,((1/(p:ℝ)) + 2*(1/(p:ℝ))^2) :=
      Finset.sum_le_sum (fun p hp => log_inverse_comparison _ (by positivity) (hpHalf hp))
    _ = (∑ p ∈ Nat.primesLE n,1/(p:ℝ)) + 2*∑ p ∈ Nat.primesLE n,1/(p:ℝ)^2 := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      linarith only [square_error_budget (Nat.primesLE n)]

/-- The fixed set of omitted primes only changes the additive constant;
its cardinality/size never grows with the sieve cutoff. -/
theorem loglog_le_outside_wheel (wheel : Finset ℕ) (n : ℕ) (hn : 2≤n) :
    Real.log (Real.log (n:ℝ)) -
      (2*squareBudget + ∑ p ∈ wheel,1/(p:ℝ)) ≤
        ∑ p ∈ Nat.primesLE n \ wheel,1/(p:ℝ) := by
  have hp : Nat.primesLE n ∩ wheel ⊆ Nat.primesLE n := Finset.inter_subset_left
  have h := Finset.sum_sdiff (f := fun p : ℕ => 1/(p:ℝ)) hp
  have he : Nat.primesLE n \ (Nat.primesLE n ∩ wheel) = Nat.primesLE n \ wheel := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [he] at h
  have hx : (∑ p ∈ Nat.primesLE n ∩ wheel,1/(p:ℝ)) ≤ ∑ p ∈ wheel,1/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => by positivity)
  linarith only [loglog_le_full n hn,h,hx]

end LinearA4OrdinaryPrimeHarmonic318
