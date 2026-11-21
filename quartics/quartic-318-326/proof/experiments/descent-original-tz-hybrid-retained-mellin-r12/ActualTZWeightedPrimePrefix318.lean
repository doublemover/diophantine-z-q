module
public import ActualTZPrimeReciprocalPrefix318
public import ActualTZSortedCollisionTelescope318
public import ActualTZWeightedCollisionLedger318
public section
noncomputable section
namespace ActualTZWeightedPrimePrefix318
open scoped BigOperators
open ActualTZPrimeReciprocalPrefix318 ActualTZSortedCollisionTelescope318
open ActualTZWeightedCollisionLedger318
attribute [local instance] Classical.propDecidable

@[expose] def reciprocalHit (hit : ℕ→Prop) (p : ℕ) : ℝ :=
  if hit p then 1/(p:ℝ) else 0

@[expose] def prefixWeight (C : ℝ) (p : ℕ) : ℝ :=
  (Real.exp C*(C/(p:ℝ)))*(1+Real.log p)^(C*Real.exp 1)

theorem weight_nonneg (C : ℝ) (hC : 0≤C) (p : ℕ) (hp : p.Prime) :
    0≤prefixWeight C p := by
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hlog := Real.log_nonneg hpR
  unfold prefixWeight
  apply mul_nonneg (by positivity)
  exact Real.rpow_nonneg (by linarith) _

/-- Pointwise true prefix-weighted loss. The event at p is not
assumed independent of any previous prime events. -/
theorem pointwise (C : ℝ) (hC : 0≤C) (S : Finset ℕ)
    (hPrime : ∀ p∈S,p.Prime) (hit : ℕ→Prop) :
    Real.exp (C*(∑ p∈S,reciprocalHit hit p))-1 ≤
      ∑ p∈S,prefixWeight C p*(if hit p then 1 else 0) := by
  classical
  let A (p : ℕ) : ℝ := C*reciprocalHit hit p
  have hA : C*(∑ p∈S,reciprocalHit hit p)=∑ p∈S,A p := by rw [A,Finset.mul_sum]
  rw [hA,exp_telescope S A]
  apply Finset.sum_le_sum
  intro p hp
  by_cases HH : hit p
  · rw [if_pos HH,mul_one]
    have hp' := hPrime p hp
    have hpR : (1:ℝ)≤p := by exact_mod_cast hp'.one_lt.le
    have hp₀ : 0<(p:ℝ) := zero_lt_one.trans_le hpR
    have hCu : C/(p:ℝ)≤C := (div_le_iff₀ hp₀).2 (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpR hC)
    have hA' : A p=C/(p:ℝ) := by simp only [A,reciprocalHit,if_pos HH,mul_one_div]
    have hHead : Real.exp (A p)-1≤Real.exp C*(C/(p:ℝ)) := by
      rw [hA']; exact exp_diff_le _ _ (by positivity) hCu
    have hSubset : S.filter (fun q=>q<p) ⊆ Nat.primesBelow p := by
      intro q hq
      exact Nat.mem_primesBelow.mpr ⟨(Finset.mem_filter.mp hq).2,
        hPrime q (Finset.mem_filter.mp hq).1⟩
    have hRec (q : ℕ) : reciprocalHit hit q≤1/(q:ℝ) := by
      by_cases hq : hit q
      · simp only [reciprocalHit,if_pos hq,le_refl]
      · simpa only [reciprocalHit,if_neg hq] using (show 0≤(1:ℝ)/(q:ℝ) by positivity)
    have hPrefix : (∑ q∈S.filter (fun q=>q<p),A q)≤
        C*(Real.exp 1*Real.log (1+Real.log p)) := by
      simp only [A,←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        _ ≤ ∑ q∈S.filter (fun q=>q<p),1/(q:ℝ) :=
          Finset.sum_le_sum (fun q _ => hRec q)
        _ ≤ ∑ q∈Nat.primesBelow p,1/(q:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun q _ _ => by positivity)
        _ ≤ _ := prefix p hp'.two_le
    have hExp : Real.exp (∑ q∈S.filter (fun q=>q<p),A q)≤
        (1+Real.log p)^(C*Real.exp 1) := by
      rw [Real.rpow_def_of_pos (by linarith [Real.log_nonneg hpR])]
      apply Real.exp_le_exp.mpr
      exact hPrefix.trans_eq (by ring)
    exact mul_le_mul hHead hExp (Real.exp_pos _).le (by positivity)
  · simp only [A,reciprocalHit,if_neg HH,mul_zero,Real.exp_zero,sub_self,zero_mul,le_refl]

/-- The exact same weights are used in each independent grid and
old wrap. The hypothesis hEvent is a per-prime CONGRUENCE MARGINAL
for the specified carrier, not a joint probability or a required
pointwise-small statement. -/
theorem wrap_average {Z R : Type*} [Fintype Z] [Fintype R]
    (S : Finset ℕ) (hP : ∀ p∈S,p.Prime) (m : Z→ℝ) (θ : Z→R→ℝ)
    (hit : Z→R→ℕ→Prop) (C : ℝ) (hC : 0≤C) (Q : ℕ→ℝ)
    (hm : ∀ z,0≤m z) (hθ : ∀ z r,0≤θ z r)
    (hEvent : ∀ p∈S,(∑ z : Z,m z*(∑ r : R,θ z r*(if hit z r p then 1 else 0)))≤Q p) :
    (∑ z : Z,m z*(∑ r : R,θ z r*
      (Real.exp (C*(∑ p∈S,reciprocalHit (hit z r) p))-1)))≤
        ∑ p∈S,prefixWeight C p*Q p := by
  classical
  let m' (w : Z×R) := m w.1*θ w.1 w.2
  let hit' (w : Z×R) (p : ℕ) := hit w.1 w.2 p
  let ℓ (w : Z×R) := Real.exp (C*(∑ p∈S,reciprocalHit (hit' w) p))-1
  have hE (p : ℕ) (hp : p∈S) :
      (∑ z : Z×R,m' z*(if hit' z p then 1 else 0))≤Q p := by
    simpa only [Fintype.sum_prod_type,m',hit',Finset.mul_sum,mul_assoc] using hEvent p hp
  have H := prime_average S m' ℓ (prefixWeight C) Q hit'
    (fun z => mul_nonneg (hm z.1) (hθ z.1 z.2))
    (fun p hp=>weight_nonneg C hC p (hP p hp))
    (fun z=>pointwise C hC S hP (hit' z)) hE
  simpa only [Fintype.sum_prod_type,m',ℓ,hit',Finset.mul_sum,mul_assoc] using H

end ActualTZWeightedPrimePrefix318
