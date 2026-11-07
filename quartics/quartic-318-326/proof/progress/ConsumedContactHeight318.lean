module
public import ContactHeight318
public import DetectorContactMap318
public section
namespace ConsumedContactHeight318
open ContactRadical318 ContactPrimeLimits318 DetectorContactMap318 ContactHeight318
open FiniteContact318 ConcretePadic318 RawWeights318 NumberField
noncomputable section
set_option maxHeartbeats 0

/-- Source-facing contract uses actual positive odd rational contacts, not
membership in an abstract or supplied radical. -/
@[expose] def ContactDivisibility (t:ℚ) (N:ℤ) (k:ℕ) : Prop :=
  ∀(p:ℕ)(hp:p.Prime),p∉badPrimes→∀(j:Fin 5)(f:ℤ),
    @rationalPlace p ⟨hp⟩ (t-root j)=f→0<f→Odd f→(p:ℤ)^k∣N

 theorem detector_height (hFive:FiveContact49Height) (t:ℚ)
    (hF:contactPolynomial t≠0) (N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k)
    (hdiv:ContactDivisibility t N k) :
    absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  apply detector_from_prime_divisibility hFive t (forms_nonzero_of_contactPolynomial t hF) N hN k hk
  intro p hpm
  have hp:=member_prime (2*t.num+t.den) t.num p hpm
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j,f,hf,hpos,hodd⟩:=member_raw_contact p t hpm
  obtain ⟨jj,hjj,hg,hho⟩:=(mem_contactPrimes _ _ p).mp hpm
  exact hdiv p hp hg j f hf hpos hodd

 theorem detector_high13 (hFive:FiveContact49Height) (t:ℚ)
    (hF:contactPolynomial t≠0) (N:ℤ) (hN:N≠0) (hdiv:ContactDivisibility t N 13) :
    absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/104) := by
  convert detector_height hFive t hF N hN 13 (by norm_num) hdiv using 1 <;> norm_num

 theorem detector_low4 (hFive:FiveContact49Height) (t:ℚ)
    (hF:contactPolynomial t≠0) (N:ℤ) (hN:N≠0) (hdiv:ContactDivisibility t N 4) :
    absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/32) := by
  convert detector_height hFive t hF N hN 4 (by norm_num) hdiv using 1 <;> norm_num

 theorem rational_point_height (t:ℚ) : pointHeight t.num t.den=absLogHeight₁ t := by
  rw [primitive_height _ _ (Rat.isCoprime_num_den t),DetectorHeightTransfer318.rational_height_eq,Rat.logHeight₁_eq_log_max]
  simp only [Nat.cast_max,Nat.cast_natAbs,Int.cast_abs,Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ)≤t.den)]

 theorem rational_from_prime_divisibility (hFive:FiveContact49Height) (t:ℚ)
    (hn:∀j:Fin 5,forms t.num t.den j≠0) (N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k)
    (hdiv:∀p∈contactPrimes t.num t.den,(p:ℤ)^k∣N) :
    absLogHeight₁ t≤HeightSeparation318.heightConstant*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  have hh:=absorbed_contact_height hFive t.num t.den (Rat.isCoprime_num_den t) hn
  rw [rational_point_height] at hh
  exact hh.le.trans (mul_le_mul_of_nonneg_left (radical_weight_bound t.num t.den N hN k hk hdiv)
    (le_trans (by norm_num : (0:ℝ)≤1) HeightSeparation318.heightConstant_ge_one))

 theorem scalar_order8 (hFive:FiveContact49Height) (t:ℚ)
    (hn:∀j:Fin 5,forms t.num t.den j≠0) (N:ℤ) (hN:N≠0)
    (hdiv:∀p∈contactPrimes t.num t.den,(p:ℤ)^8∣N) :
    absLogHeight₁ t≤HeightSeparation318.heightConstant*|(N:ℝ)|^((49:ℝ)/64) := by
  convert rational_from_prime_divisibility hFive t hn N hN 8 (by norm_num) hdiv using 1 <;> norm_num

 theorem rational_zero_height (N:ℤ) (k:ℕ) :
    absLogHeight₁ (0:ℚ)≤HeightSeparation318.heightConstant*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  rw [DetectorHeightTransfer318.rational_height_eq,Rat.logHeight₁_eq_log_max]
  norm_num
  exact mul_nonneg (le_trans (by norm_num : (0:ℝ)≤1) HeightSeparation318.heightConstant_ge_one)
    (Real.rpow_nonneg (abs_nonneg _) _)

end
end ConsumedContactHeight318
#print axioms ConsumedContactHeight318.detector_height
#print axioms ConsumedContactHeight318.scalar_order8
