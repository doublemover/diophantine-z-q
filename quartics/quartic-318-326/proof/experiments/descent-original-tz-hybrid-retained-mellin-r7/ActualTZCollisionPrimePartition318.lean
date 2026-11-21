module
public import ActualTZPhysicalCorrectionBound318
public import ActualTZWeightedPrimePrefix318
import all ActualTZPhysicalEulerSplit318
public section
noncomputable section
namespace ActualTZCollisionPrimePartition318
open scoped BigOperators
open ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZWeightedPrimePrefix318
attribute [local instance] Classical.propDecidable

def regular (y N K : ℕ) : Finset ℕ :=
  (Nat.primesBelow (2*N+1)).filter (fun p=>y<p ∧ ¬p∣K)

def extra (W P K : ℕ) : ℝ :=
  ∑ p∈(offWheel W P).filter (fun p=>p∣K),1/(p:ℝ)

theorem extra_nonneg (W P K : ℕ) : 0≤extra W P K := by
  unfold extra
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem regular_prime (y N K : ℕ) (p : ℕ) (hp : p∈regular y N K) : p.Prime :=
  Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1

theorem hit_nonnegative (hit : ℕ→Prop) (p : ℕ) : 0≤reciprocalHit hit p := by
  unfold reciprocalHit
  split_ifs <;> positivity

/-- When the wheel covers all p≤y, remove the exceptional marker
divisors BEFORE applying the positive prefix telescope. A nonzero
actual long cell may supply the horizon only when its weight is
positive; no claim is made for empty/excluded cells. -/
theorem split (W P y N K : ℕ) (hit : ℕ→Prop)
    (hW : ∀ p,p.Prime→p≤y→p∣W)
    (hH : ∀ p∈offWheel W P,hit p→p≤2*N) :
    (∑ p∈offWheel W P,reciprocalHit hit p) ≤
      extra W P K+(∑ p∈regular y N K,reciprocalHit hit p) := by
  classical
  let Q : Finset ℕ := offWheel W P
  let A := Q.filter (fun p=>p∣K)
  let B := Q.filter (fun p=>¬p∣K)
  have hQ : (∑ p∈Q,reciprocalHit hit p) =
      (∑ p∈A,reciprocalHit hit p)+(∑ p∈B,reciprocalHit hit p) :=
    (Finset.sum_filter_add_sum_filter_not Q (fun p=>p∣K) (reciprocalHit hit)).symm
  have hA : (∑ p∈A,reciprocalHit hit p)≤extra W P K := by
    apply Finset.sum_le_sum
    intro p _
    unfold reciprocalHit
    split_ifs
    · exact le_rfl
    · positivity
  have hB : (∑ p∈B,reciprocalHit hit p)≤∑ p∈regular y N K,reciprocalHit hit p := by
    let C := B.filter hit
    have hC : (∑ p∈B,reciprocalHit hit p)=∑ p∈C,reciprocalHit hit p := by
      rw [C,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : hit p
      · rw [if_pos hp]
      · rw [if_neg hp,reciprocalHit,if_neg hp]
    rw [hC]
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun p _ _=>hit_nonnegative hit p)
    intro p hp
    obtain ⟨hB,hHit⟩ := Finset.mem_filter.mp hp
    obtain ⟨hQ,hK⟩ := Finset.mem_filter.mp hB
    obtain ⟨hP,hc⟩ := Finset.mem_filter.mp hQ
    have hPrime := Nat.prime_of_mem_primesBelow hP
    have hY : y<p := by
      by_contra hy
      have hdiv := hW p hPrime (by omega)
      exact (hPrime.dvd_iff_not_coprime.mp hdiv) hc.symm
    have hHorizon : p<2*N+1 := by
      have h := hH p hQ hHit
      omega
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨hHorizon,hPrime⟩,hY,hK⟩
  rw [hQ]
  exact add_le_add hA hB

end ActualTZCollisionPrimePartition318
