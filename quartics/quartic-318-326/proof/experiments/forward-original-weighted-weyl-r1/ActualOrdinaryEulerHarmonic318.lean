module
public import ActualGlobalCharacterLower318
public section
noncomputable section
namespace ActualOrdinaryEulerHarmonic318
open scoped BigOperators
set_option maxHeartbeats 20000000

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
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    h1 hmul prime_reciprocal_norm_summable (Finset.range N)).2
  convert hh using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (prime_reciprocal_series p (Finset.mem_filter.mp hp).2).tsum_eq.symm

lemma actual_harmonic_le_euler (N : ℕ) :
    (∑n∈Finset.Ico 1 N,(n:ℝ)⁻¹)≤ordinaryFull N := by
  classical
  let f : ↥(Finset.Ico 1 N) → Nat.factoredNumbers (Finset.range N) := fun n =>
    ⟨n.1,Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by have hh := Finset.mem_Ico.mp n.2;omega,
      fun p hpn _ _ => Finset.mem_range.mpr (hpn.trans_lt (Finset.mem_Ico.mp n.2).2)⟩⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hh := hasSum_le_inj f hf (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.1))
    (fun _ => le_rfl)
    (hasSum_fintype (fun n : ↥(Finset.Ico 1 N) => (n.1:ℝ)⁻¹))
    (actual_finite_reciprocal_euler N)
  simpa only [Finset.sum_coe_sort] using hh

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
  simpa only [Nat.cast_add,Nat.cast_one] using ht

end ActualOrdinaryEulerHarmonic318
