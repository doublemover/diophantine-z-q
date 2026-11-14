module
public import SelectedProductDepth318
public section
noncomputable section
namespace SelectedContactWeightValues318
open ConcretePadic318 DetectorPrimeProduct318 ScaledContactWeights318 DetectorWeightPreparation318
open ConcreteG8Domain (pair)
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma small_unit (n : ℕ) (hn : 0<n) (hnp : n<p) : rationalPlace p (n:ℚ)=0 :=
  rational_nat_unit p n (fun hd => (not_le_of_gt hnp) (Nat.le_of_dvd hn hd))

/-- All fixed contact-minus-one constants are units for the original
large-prime range. This is checked on the actual five rational contacts. -/
theorem theta_minus_one (hp : 76176<p) (i : Fin 5) :
    rationalPlace p (theta i-1)=0 := by
  have h2 := small_unit p 2 (by norm_num) (by omega)
  have h3 := small_unit p 3 (by norm_num) (by omega)
  have h2398 := small_unit p 2398 (by norm_num) (by omega)
  have h2399 := small_unit p 2399 (by norm_num) (by omega)
  have h439 := small_unit p 439 (by norm_num) (by omega)
  have h407 := small_unit p 407 (by norm_num) (by omega)
  fin_cases i
  · norm_num [theta]
  · have he : theta 1-1= -(3:ℚ)/2 := by norm_num [theta]
    rw [he,(rationalPlace p).map_div,(rationalPlace p).map_neg,h3,h2,sub_self]
  · have he : theta 2-1= -(2:ℚ) := by norm_num [theta]
    rw [he,(rationalPlace p).map_neg,h2]
  · have he : theta 3-1= -(2398:ℚ)/2399 := by norm_num [theta]
    rw [he,(rationalPlace p).map_div,(rationalPlace p).map_neg,h2398,h2399,sub_self]
  · have he : theta 4-1= -(439:ℚ)/407 := by norm_num [theta]
    rw [he,(rationalPlace p).map_div,(rationalPlace p).map_neg,h439,h407,sub_self]

lemma selected_delta (hp : 76176<p) (c u d : ℚ) (hc : c≠0) (hd : d≠0)
    (hcunit : rationalPlace p c=0) (hdunit : rationalPlace p d=0)
    (i : Fin 5) (hselected : rationalPlace p (linear c u d i)=1) :
    rationalPlace p (delta c (u/d^2))=0 := by
  have he : parameter c (u/d^2)-theta i=c^2/d^2*linear c u d i := by
    unfold parameter linear
    field_simp [hc,hd] <;> ring
  have hv : rationalPlace p (parameter c (u/d^2)-theta i)=1 := by
    rw [he,(rationalPlace p).map_mul,(rationalPlace p).map_div,
      (rationalPlace p).map_pow,(rationalPlace p).map_pow,hcunit,hdunit,hselected]
    norm_num
  have htheta := theta_minus_one p hp i
  have heq : delta c (u/d^2)=(parameter c (u/d^2)-theta i)+(theta i-1) := by
    unfold delta
    ring
  rw [heq,(rationalPlace p).map_add_of_distinct_val (by rw [hv,htheta]; norm_num),hv,htheta]
  norm_num

/-- The actual product of five selected primes gives the original three
NEGATIVE ODD weight values −1,−7,−25. No arbitrary weight is supplied. -/
theorem weight_values (c u d : ℚ) (hc : c≠0) (hd : d≠0)
    (hcunit : rationalPlace p c=0) (hdunit : rationalPlace p d=0)
    (hdelta : rationalPlace p (delta c (u/d^2))=0)
    (k : Fin 5 → ℤ) (hk : ∀ i, linear c u d i=(k i:ℚ))
    (hproduct : rationalPlace p (DetectorPrimeProduct318.product k:ℚ)=1) :
    rationalPlace p (weights c (u/d^2) 0)= -1 ∧
    rationalPlace p (weights c (u/d^2) 1)= -7 ∧
    rationalPlace p (weights c (u/d^2) 2)= -25 := by
  have hf : rationalPlace p (ContactWeightWitness318.contact (parameter c (u/d^2)))=1 := by
    rw [contact_product c u d hc hd,hk 0,hk 1,hk 2,hk 3,hk 4,←product_cast,
      (rationalPlace p).map_mul,(rationalPlace p).map_div,
      (rationalPlace p).map_pow,(rationalPlace p).map_pow,hcunit,hdunit,hproduct]
    norm_num
  have hq : rationalPlace p (scaledWeight c (u/d^2))= -1 := by
    rw [scaledWeight,ContactWeightWitness318.weight,(rationalPlace p).map_mul,
      (rationalPlace p).map_div,(rationalPlace p).map_pow,(rationalPlace p).map_pow,
      hcunit,hf]
    have hdelt : rationalPlace p (parameter c (u/d^2)-1)=0 := hdelta
    rw [hdelt]
    norm_num
  refine ⟨hq,?_,?_⟩
  · change rationalPlace p ((scaledWeight c (u/d^2))^7*(delta c (u/d^2))^18)=_
    rw [(rationalPlace p).map_mul,(rationalPlace p).map_pow,
      (rationalPlace p).map_pow,hq,hdelta]
    norm_num
  · change rationalPlace p ((scaledWeight c (u/d^2))^25*(delta c (u/d^2))^72)=_
    rw [(rationalPlace p).map_mul,(rationalPlace p).map_pow,
      (rationalPlace p).map_pow,hq,hdelta]
    norm_num

lemma all_odd (rho : ℚ_[p]) (hr : rho^2=2) (c t : ℚ)
    (hw : rationalPlace p (weights c t 0)= -1 ∧
      rationalPlace p (weights c t 1)= -7 ∧ rationalPlace p (weights c t 2)= -25) :
    ∀ j : Fin 3, ValuationEvenNormChain.OddAt (place p rho hr) (pair (weights c t j) 0) := by
  intro j
  fin_cases j
  · exact ⟨-1,by simpa only [place_rational] using hw.1,by decide⟩
  · exact ⟨-7,by simpa only [place_rational] using hw.2.1,by decide⟩
  · exact ⟨-25,by simpa only [place_rational] using hw.2.2,by decide⟩

end SelectedContactWeightValues318
