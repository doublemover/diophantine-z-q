module
public import ActualTZRegulatedLocalFactor318
public import ActualTZMultiLinearCRT318
import all ActualTZMultiLinearCRT318
import all ActualTZRegulatedLocalFactor318
public section
noncomputable section
namespace ActualTZRegulatedPhysicalPrime318
open scoped BigOperators
open ActualTZRegulatedLocalFactor318
open ActualTZMultiLinearCRT318 (physicalConst assigned_roots_agree)
attribute [local instance] Classical.propDecidable

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K]

@[expose] def primeRoot (W p : ℕ) (a : I → ℤ) (b : I → ℕ) (i : I) : ZMod p :=
  ((-Nat.gcdA W p * physicalConst W a b i : ℤ) : ZMod p)

theorem root_collision (W p : ℕ) (a : I → ℤ) (b : I → ℕ)
    (i j : I) (hc : W.Coprime p) :
    primeRoot W p a b i = primeRoot W p a b j ↔
      (p : ℤ) ∣ physicalConst W a b i - physicalConst W a b j := by
  simp only [primeRoot,ZMod.intCast_eq_intCast_iff]
  exact assigned_roots_agree W p _ _ hc

theorem root_hit (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (i : I) (x : ZMod p) (hc : W.Coprime p) :
    primeRoot W p a b i = x ↔ (p : ℤ) ∣ (W : ℤ) * (x.val : ℤ) + physicalConst W a b i := by
  have hx : ((x.val : ℤ) : ZMod p) = x := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val x
  calc
    primeRoot W p a b i = x ↔ primeRoot W p a b i = ((x.val : ℤ) : ZMod p) := by
      rw [hx]
    _ ↔ _ := by
      rw [primeRoot,ZMod.intCast_eq_intCast_iff]
      exact (ActualTZOneLinearDivisorCRT318.bezout_class W p _ _ hc).symm

def physicalMass (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (d e : Bits I) : K :=
  (∑ x : ZMod p, if ∀ i, selected d e i →
    (p : ℤ) ∣ (W : ℤ) * (x.val : ℤ) + physicalConst W a b i then 1 else 0)/(p : K)

theorem physicalMass_good (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (d e : Bits I) (hc : W.Coprime p) :
    (physicalMass W p a b d e : K) = acceptedMass (primeRoot W p a b) d e := by
  unfold physicalMass acceptedMass
  rw [ZMod.card]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have h : (∀ i, selected d e i →
    (p : ℤ) ∣ (W : ℤ) * (x.val : ℤ) + physicalConst W a b i) ↔
      accepts (primeRoot W p a b) x d e := by
    exact ⟨fun H i hi => (root_hit W p a b i x hc).mpr (H i hi),
      fun H i hi => (root_hit W p a b i x hc).mp (H i hi)⟩
  simp only [h]

/-- For primes away from W, this is the actual signed Euler factor.
The constant of every row is the original W*a_i+b_i on the same
shared x-cell, including any fixed integer wrap shift in a_i. -/
theorem local_good (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (z w : I → K) (hc : W.Coprime p) :
    (∑ d : Bits I,∑ e : Bits I,amplitude z w d e * physicalMass W p a b d e) =
      1 + (∑ x : ZMod p, ((∏ i : I, if primeRoot W p a b i = x then
        (1-z i)*(1-w i) else 1) - 1))/(p : K) := by
  simp_rw [physicalMass_good W p a b _ _ hc]
  simpa only [ZMod.card] using residue_factor (primeRoot W p a b) z w

theorem physicalMass_incident (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (d e : Bits I) (hc : W.Coprime p) :
    (physicalMass W p a b d e : K) = if ∀ i, ¬selected d e i then 1 else
      if ∀ i j, selected d e i → selected d e j →
        (p : ℤ) ∣ physicalConst W a b i - physicalConst W a b j
      then 1/(p : K) else 0 := by
  rw [physicalMass_good W p a b d e hc,acceptedMass_eq,ZMod.card]
  simp only [root_collision W p a b _ _ hc]

/-- If p divides none of the original pair differences, two distinct
positions can never ask for p simultaneously. Both slots at a SINGLE
position are still allowed. -/
theorem no_cross_position (W p : ℕ) (a : I → ℤ) (b : I → ℕ)
    (d e : Bits I) (hc : W.Coprime p)
    (hDiff : ∀ i j,i ≠ j → ¬(p : ℤ) ∣ physicalConst W a b i - physicalConst W a b j)
    (x : ZMod p) (h : accepts (primeRoot W p a b) x d e) :
    ∀ i j, selected d e i → selected d e j → i = j := by
  intro i j hi hj
  by_contra hn
  exact hDiff i j hn ((root_collision W p a b i j hc).mp ((h i hi).trans (h j hj).symm))

/-- For an already specialized distinct physical tuple, every
cross-position collision prime lies among the prime factors of these
actual nonzero signed differences. Formal polynomial distinctness
before specialization alone does not imply this hypothesis. -/
def collisionPrimes (W : ℕ) (a : I → ℤ) (b : I → ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (I × I)).filter fun ij => ij.1 ≠ ij.2).biUnion
    fun ij => (physicalConst W a b ij.1 - physicalConst W a b ij.2).natAbs.primeFactors

theorem root_injective_off (W p : ℕ) (a : I → ℤ) (b : I → ℕ)
    (hp : p.Prime) (hc : W.Coprime p) (hd : Function.Injective (physicalConst W a b))
    (hf : p ∉ collisionPrimes W a b) : Function.Injective (primeRoot W p a b) := by
  intro i j hr
  by_contra hn
  let Δ := physicalConst W a b i - physicalConst W a b j
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr (fun H => hn (hd H))
  have hdz : (p : ℤ) ∣ Δ := (root_collision W p a b i j hc).mp hr
  have hdN : p ∣ Δ.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdz)
  apply hf
  exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,
    Nat.mem_primeFactors.mpr ⟨hp,hdN,fun H => hΔ (Int.natAbs_eq_zero.mp H)⟩⟩

theorem local_distinct (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (z w : I → K) (hp : p.Prime) (hc : W.Coprime p)
    (hd : Function.Injective (physicalConst W a b)) (hf : p ∉ collisionPrimes W a b) :
    (∑ d : Bits I,∑ e : Bits I,amplitude z w d e * physicalMass W p a b d e) =
      1 + (∑ i : I, ((1-z i)*(1-w i)-1))/(p : K) := by
  rw [local_good W p a b z w hc,distinct_correction _ (root_injective_off W p a b hp hc hd hf)]

theorem physicalMass_bad (W p : ℕ) [NeZero p] (a : I → ℤ) (b : I → ℕ)
    (d e : Bits I) (hUnit : ∀ i,W.Coprime (b i)) (hc : ¬W.Coprime p) :
    (physicalMass W p a b d e : K) = if ∀ i, ¬selected d e i then 1 else 0 := by
  unfold physicalMass
  by_cases h0 : ∀ i, ¬selected d e i
  · have h (x : ZMod p) : ∀ i,selected d e i →
        (p : ℤ) ∣ (W : ℤ)*(x.val : ℤ)+physicalConst W a b i := fun i hi => (h0 i hi).elim
    have hp : (p : K) ≠ 0 := by exact_mod_cast NeZero.ne p
    simp only [h,if_pos h0,if_true,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_one,div_self hp]
  · obtain ⟨i,hi⟩ : ∃ i,selected d e i := by simpa only [not_forall,not_not] using h0
    have h (x : ZMod p) : ¬(∀ i,selected d e i →
        (p : ℤ) ∣ (W : ℤ)*(x.val : ℤ)+physicalConst W a b i) := by
      intro H
      apply ActualTZOneLinearDivisorCRT318.noncoprime_no_hit W p (b i) (hUnit i) hc _ (a i)
      simpa only [physicalConst,mul_add,add_assoc] using H i hi
    simp only [h,if_neg h0,if_false,Finset.sum_const_zero,zero_div]

end ActualTZRegulatedPhysicalPrime318
