module
public import ActualSamePositionDivisors318
public section
noncomputable section
namespace ActualSamePositionBoxTail318
open scoped BigOperators
open IntegerResidueBoxCount318 ActualSquareDivisibleValues318 ActualSamePositionDivisors318
open ActualDivisorSubpower318
set_option maxHeartbeats 15000000

lemma prime_count_bound (B Y : ℕ) (b : Interval B) (δ : ℝ) (hδ : 0<δ) :
    ((primes b.1 Y).card:ℝ)≤divisorConstant δ*((B:ℝ)^2+1)^δ := by
  have hc : (primes b.1 Y).card≤(normValue b.1).divisors.card := Finset.card_filter_le _ _
  have hv : (normValue b.1:ℝ)≤(B:ℝ)^2+1 := by
    have hs := OriginalBadSliceLogWeight318.square_bound B b.1 (Finset.mem_Icc.mp b.2)
    have hh : (normValue b.1:ℤ)≤(B:ℤ)^2+1 := by rw [normValue_cast];linarith
    exact_mod_cast hh
  have hr := Real.rpow_le_rpow (by positivity) hv hδ.le
  exact (show ((primes b.1 Y).card:ℝ)≤((normValue b.1).divisors.card:ℝ) by exact_mod_cast hc).trans
    ((actual_divisor_subpower δ hδ (normValue b.1) (normValue_pos b.1).ne').trans
      (mul_le_mul_of_nonneg_left hr (divisorConstant_pos δ hδ).le))

/-- The nonzero a coordinate has no additive residue-boundary term:
its actual sign/positive-quotient count retains the full1/p saving. -/
lemma actual_multiple_bound (B Y : ℕ) (hY : 0<Y) (b : Interval B) (p : ↥(primes b.1 Y)) :
    (Nat.card (Values B p.1):ℝ)≤2*(B:ℝ)/(Y:ℝ) := by
  have hp := (Finset.mem_filter.mp p.2).2
  have hh := actual_scaled_multiple_count B p.1 hp.1.pos
  have hpR : (0:ℝ)<p.1 := by exact_mod_cast hp.1.pos
  have hYR : (0:ℝ)<Y := by exact_mod_cast hY
  have hc : (Nat.card (Values B p.1):ℝ)≤2*(B:ℝ)/(p.1:ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast hh
  exact hc.trans (div_le_div_of_nonneg_left (by positivity) hYR
    (by exact_mod_cast hp.2.le))

@[expose] def countBudget (B Y : ℕ) (δ : ℝ) : ℝ :=
  (2*(B:ℝ)+1)^2*(1+(2*(B:ℝ)/(Y:ℝ))*divisorConstant δ*((B:ℝ)^2+1)^δ)

/-- Complete original same-position source, INCLUDING a=0. The b²+1
value is strictly positive, so its actual finite divisor set is valid at
b=0 and every negative b as well. No generic coprime-box sieve is assumed. -/
theorem actual_same_position_count (B Y : ℕ) (hY : 2≤Y) (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (Source B Y):ℝ)≤countBudget B Y δ := by
  classical
  have hY0 : 0<Y := by omega
  have hC : 0≤2*(B:ℝ)/(Y:ℝ) := by positivity
  have hD := (divisorConstant_pos δ hδ).le
  have hN : 0≤((B:ℝ)^2+1)^δ := Real.rpow_nonneg (by positivity) _
  have hI : Nat.card (Interval B)=2*B+1 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Interval] using interval_card B
  have hf (b : Interval B) :
      (∑ p : ↥(primes b.1 Y),(Nat.card (Values B p.1):ℝ)*(2*(B:ℝ)+1))≤
        (divisorConstant δ*((B:ℝ)^2+1)^δ)*
          ((2*(B:ℝ)/(Y:ℝ))*(2*(B:ℝ)+1)) := by
    calc
      _ ≤ ∑ _p : ↥(primes b.1 Y),(2*(B:ℝ)/(Y:ℝ))*(2*(B:ℝ)+1) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right
          (actual_multiple_bound B Y hY0 b p) (by positivity))
      _ = ((primes b.1 Y).card:ℝ)*((2*(B:ℝ)/(Y:ℝ))*(2*(B:ℝ)+1)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (prime_count_bound B Y b δ hδ) (by positivity)
  have hs := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hf b)
  have hc := Nat.card_le_card_of_injective (sourceChoice B Y hY) (choice_injective B Y hY)
  have he : (Nat.card (Target B Y):ℝ)=(2*(B:ℝ)+1)^2+
      ∑ b : Interval B,∑ p : ↥(primes b.1 Y),
        (Nat.card (Values B p.1):ℝ)*(2*(B:ℝ)+1) := by
    simp only [Target,Nat.card_eq_fintype_card,Fintype.card_sum,
      Fintype.card_sigma,Fintype.card_prod,Nat.cast_add,Nat.cast_mul,Nat.cast_sum]
    simp only [←Nat.card_eq_fintype_card,hI,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    ring
  have hcR : (Nat.card (Source B Y):ℝ)≤(Nat.card (Target B Y):ℝ) := by exact_mod_cast hc
  rw [he] at hcR
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hI,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hs
  dsimp [countBudget]
  nlinarith only [hcR,hs]

end ActualSamePositionBoxTail318
