module
public import FiniteBernoulliEulerMoment318
public import Mathlib.NumberTheory.Chebyshev
public section
noncomputable section
namespace ActualChebyshevLogMoment318
open scoped BigOperators
set_option maxHeartbeats 15000000

@[expose] def partialMass (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n∈Finset.range N,a (n+1)
@[expose] def weightedPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n∈Finset.range N,a (n+1)/((n:ℝ)+1)
lemma prefix_succ (a : ℕ → ℝ) (N : ℕ) : partialMass a (N+1)=partialMass a N+a (N+1) := by
  exact Finset.sum_range_succ _ _
lemma weightedPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    weightedPrefix a (N+1)=weightedPrefix a N+a (N+1)/((N:ℝ)+1) := by
  exact Finset.sum_range_succ _ _

/-- Finite Abel summation with the exact terminal term; no asymptotic
partial-summation input is assumed. -/
theorem exact_partial_summation (a : ℕ → ℝ) (N : ℕ) :
    weightedPrefix a (N+1)=partialMass a (N+1)/((N:ℝ)+1)+
      ∑ n∈Finset.range N,partialMass a (n+1)*(1/((n:ℝ)+1)-1/((n:ℝ)+2)) := by
  induction N with
  | zero => simp [partialMass,weightedPrefix]
  | succ N ih =>
    rw [weightedPrefix_succ,ih,Finset.sum_range_succ,prefix_succ a (N+1)]
    push_cast
    have h1 : (N:ℝ)+1≠0 := by positivity
    have h2 : (N:ℝ)+2≠0 := by positivity
    field_simp [h1,h2]
    <;> ring

lemma reciprocal_log_step (x : ℝ) (hx : 0<x) :
    1/(x+1)≤Real.log (x+1)-Real.log x := by
  have hx1 : 0<x+1 := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hx1)
  rw [Real.log_div hx.ne' hx1.ne'] at hh
  have he : x/(x+1)-1= -(1/(x+1)) := by field_simp [hx1.ne'];ring
  rw [he] at hh
  linarith
lemma actual_harmonic_prefix (N : ℕ) :
    (∑ n∈Finset.range N,1/((n:ℝ)+2))≤Real.log ((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := reciprocal_log_step ((N:ℝ)+1) (by positivity)
    push_cast
    have he : (N:ℝ)+1+1=(N:ℝ)+2 := by ring
    rw [he] at hs
    linarith

/-- A linear bound on the exact partialMass yields an explicit logarithmic
bound on its reciprocal-weighted partialMass, including N=1. -/
theorem weighted_prefix_bound (a : ℕ → ℝ) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ N,partialMass a N≤C*(N:ℝ)) (N : ℕ) :
    weightedPrefix a (N+1)≤C*(1+Real.log ((N:ℝ)+1)) := by
  rw [exact_partial_summation]
  have hlast : partialMass a (N+1)/((N:ℝ)+1)≤C := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(N:ℝ)+1)).mpr
    simpa only [Nat.cast_add,Nat.cast_one] using hbound (N+1)
  have hterm (n : ℕ) : partialMass a (n+1)*(1/((n:ℝ)+1)-1/((n:ℝ)+2))≤C/((n:ℝ)+2) := by
    have hd : 0≤1/((n:ℝ)+1)-1/((n:ℝ)+2) := sub_nonneg.mpr
      (one_div_le_one_div_of_le (by positivity) (by linarith))
    have hh := mul_le_mul_of_nonneg_right (hbound (n+1)) hd
    calc
      _ ≤ C*((n:ℝ)+1)*(1/((n:ℝ)+1)-1/((n:ℝ)+2)) := by
        simpa only [Nat.cast_add,Nat.cast_one] using hh
      _ = _ := by
        have h1 : (n:ℝ)+1≠0 := by positivity
        have h2 : (n:ℝ)+2≠0 := by positivity
        field_simp [h1,h2]
        <;> ring
  have hs := Finset.sum_le_sum (fun n (_ : n∈Finset.range N) => hterm n)
  have he : (∑ n∈Finset.range N,C/((n:ℝ)+2))=C*∑ n∈Finset.range N,1/((n:ℝ)+2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he] at hs
  have hl := mul_le_mul_of_nonneg_left (actual_harmonic_prefix N) hC
  nlinarith only [hlast,hs,hl]

@[expose] def primeLog (p : ℕ) : ℝ := if p.Prime then Real.log (p:ℝ) else 0
lemma primeLog_nonneg (p : ℕ) : 0≤primeLog p := by
  dsimp [primeLog]
  split_ifs
  · exact Real.log_natCast_nonneg p
  · exact le_rfl

/-- Exact equality with the pinned Chebyshev theta, not an unrelated
prime distribution predicate. -/
lemma actual_theta_prefix (N : ℕ) : partialMass primeLog N=Chebyshev.theta (N:ℝ) := by
  rw [Chebyshev.theta,Nat.floor_natCast,Finset.sum_filter]
  unfold partialMass
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    apply Finset.mem_Ioc.mpr
    have hh := Finset.mem_range.mp hn
    omega
  · intro n _ k _ he
    omega
  · intro p hp
    have hh := Finset.mem_Ioc.mp hp
    refine ⟨p-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro n _
    rfl
lemma actual_theta_bound (N : ℕ) : partialMass primeLog N≤Real.log 4*(N:ℝ) := by
  rw [actual_theta_prefix]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

lemma interval_weighted_prefix (N : ℕ) :
    (∑ p∈Finset.Ioc 0 N,primeLog p/(p:ℝ))=weightedPrefix primeLog N := by
  symm
  unfold weightedPrefix
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    apply Finset.mem_Ioc.mpr
    have hh := Finset.mem_range.mp hn
    omega
  · intro n _ k _ he
    omega
  · intro p hp
    have hh := Finset.mem_Ioc.mp hp
    refine ⟨p-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro n _
    simp only [Nat.cast_add,Nat.cast_one]

/-- Actual finite prime log moment for ANY retained subset, including
removal of one prime. The only input is the set's real prime/range facts. -/
theorem actual_prime_log_moment (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hS : ∀ p∈S,p.Prime ∧ p≤N) :
    (∑ p∈S,Real.log (p:ℝ)/(p:ℝ))≤Real.log 4*(1+Real.log (N:ℝ)) := by
  have hsub : S⊆Finset.Ioc 0 N := by
    intro p hp
    exact Finset.mem_Ioc.mpr ⟨(hS p hp).1.pos,(hS p hp).2⟩
  have hs : (∑ p∈S,Real.log (p:ℝ)/(p:ℝ))≤
      ∑ p∈Finset.Ioc 0 N,primeLog p/(p:ℝ) := by
    calc
      _ = ∑ p∈S,primeLog p/(p:ℝ) := Finset.sum_congr rfl
        (fun p hp => by rw [primeLog,if_pos (hS p hp).1])
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg (primeLog_nonneg p) (Nat.cast_nonneg p))
  rw [interval_weighted_prefix] at hs
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  exact hs.trans (by simpa only [Nat.cast_succ] using
    weighted_prefix_bound primeLog (Real.log 4) (Real.log_nonneg (by norm_num)) actual_theta_bound n)

end ActualChebyshevLogMoment318
