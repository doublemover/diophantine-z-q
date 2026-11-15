module
public import ActualSeventeenEntry318
public section
noncomputable section
namespace SeventeenOrbitPrecision318
open ConcreteG8Domain (K D pair i)
open ValuativeOrbitBounds318
open CoherentMultipleCharts318 (chartU chartV)
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

lemma two_value : Padic.addValuation (2:ℚ_[17])=0 := by
  have he := ConcretePadic318.rational_nat_unit 17 2 (by norm_num)
  rw [PadicDetectorCoefficients318.rational_embedding] at he
  simpa using he

lemma root_value (ρ : ℚ_[17]) (hρ : ρ^2=2) : Padic.addValuation ρ=0 := by
  have hn : ρ≠0 := by intro he; rw [he] at hρ; norm_num at hρ
  have he := congrArg Padic.addValuation hρ
  rw [Padic.addValuation.map_pow,Padic.addValuation.apply hn,two_value,two_nsmul] at he
  have hi : ρ.valuation+ρ.valuation=0 := by exact_mod_cast he
  have hz : ρ.valuation=0 := by omega
  rw [Padic.addValuation.apply hn,hz]
  rfl

lemma pair_bound (ρ : ℚ_[17]) (hρ : ρ^2=2) (r : ℤ) (a b : ℚ)
    (ha : (r:WithTop ℤ)≤ConcretePadic318.rationalPlace 17 a)
    (hb : (r:WithTop ℤ)≤ConcretePadic318.rationalPlace 17 b) :
    Bound (ConcretePadic318.place 17 ρ hρ) r (pair a b) := by
  unfold Bound
  rw [ConcretePadic318.place_pair]
  rw [PadicDetectorCoefficients318.rational_embedding] at ha hb
  have hr : Bound Padic.addValuation 0 ρ := by rw [Bound,root_value ρ hρ]
  exact badd Padic.addValuation ha (bmul_unit Padic.addValuation hb hr)

lemma coefficient_bound (q : ℚ) (r : ℤ) (hr : 1≤r) (hq : padicValRat 17 q=r) :
    (1:WithTop ℤ)≤ConcretePadic318.rationalPlace 17 q := by
  have hn : q≠0 := by intro hz; rw [hz] at hq; simp at hq; omega
  rw [ConcretePadic318.rational_value 17 q hn,hq]
  exact_mod_cast hr

lemma entry (ρ : ℚ_[17]) (hρ : ρ^2=2) :
    Near (ConcretePadic318.place 17 ρ hρ) 1 (chartU 20) (chartV 20) := by
  constructor
  · change Bound (ConcretePadic318.place 17 ρ hρ) 1 (pair (chartU 20).re (chartU 20).im)
    exact pair_bound ρ hρ 1 _ _
      (coefficient_bound _ 1 (by omega) ActualSeventeenEntry318.u_real_depth)
      (coefficient_bound _ 1 (by omega) ActualSeventeenEntry318.u_imaginary_depth)
  · change Bound (ConcretePadic318.place 17 ρ hρ) 1 (pair (chartV 20-1).re (chartV 20-1).im)
    exact pair_bound ρ hρ 1 _ _
      (coefficient_bound _ 4 (by omega) ActualSeventeenEntry318.v_real_depth)
      (coefficient_bound _ 4 (by omega) ActualSeventeenEntry318.v_imaginary_depth)

lemma nat_integral (ρ : ℚ_[17]) (hρ : ρ^2=2) (n : ℕ) :
    Bound (ConcretePadic318.place 17 ρ hρ) 0 (n:K) := bnat _ n

lemma D_integral (ρ : ℚ_[17]) (hρ : ρ^2=2) :
    Bound (ConcretePadic318.place 17 ρ hρ) 0 D := by
  have hi : Bound (ConcretePadic318.place 17 ρ hρ) 0 i := by
    change 0≤ConcretePadic318.place 17 ρ hρ (pair 0 1)
    rw [ConcretePadic318.place_pair]
    simp only [Rat.cast_zero,Rat.cast_one,zero_add,one_mul,root_value ρ hρ]
    exact le_rfl
  have he := bsquare (ConcretePadic318.place 17 ρ hρ)
    (bsub _ (nat_integral ρ hρ 3) hi)
  simpa only [mul_zero,ConcreteG8Domain.D] using he

lemma prime_value (ρ : ℚ_[17]) (hρ : ρ^2=2) :
    Bound (ConcretePadic318.place 17 ρ hρ) 1 (17:K) := by
  have he : (17:K)=pair 17 0 := by ext <;> norm_num [pair]
  rw [Bound,he,ConcretePadic318.place_rational,ConcretePadic318.rational_value 17 _ (by norm_num),
    padicValRat.self (by norm_num)]
  exact le_rfl

/-- The actual index20 entry, followed by17-power multiplication, now
produces every local precision at either conjugate place. -/
theorem place_precision (ρ : ℚ_[17]) (hρ : ρ^2=2) (e : ℕ) (m : ℤ) :
    Near (ConcretePadic318.place 17 ρ hρ) ((e:ℤ)+1)
      (chartU (20*17^e*m)) (chartV (20*17^e*m)) := by
  have he := ValuativeOrbitMultiples318.prime_power_multiples
    (ConcretePadic318.place 17 ρ hρ) 17 (prime_value ρ hρ) 20 (D_integral ρ hρ) (entry ρ hρ) e m
  simpa only [mul_comm (17:ℤ)^e 20] using he

/-- Both conjugate field bounds recover each original rational coefficient.
The denominators2 and2rho are genuine units at17. -/
lemma recover_coefficients (ρ : ℚ_[17]) (hρ : ρ^2=2) (r : ℤ) (x : K)
    (hp : Bound (ConcretePadic318.place 17 ρ hρ) r x)
    (hn : Bound (ConcretePadic318.place 17 (-ρ) (ConcretePadic318.negative_root 17 ρ hρ)) r x) :
    (r:WithTop ℤ)≤ConcretePadic318.rationalPlace 17 x.re ∧
    (r:WithTop ℤ)≤ConcretePadic318.rationalPlace 17 x.im := by
  have hρ0 : ρ≠0 := by intro he; rw [he] at hρ; norm_num at hρ
  change Bound (ConcretePadic318.place 17 ρ hρ) r (pair x.re x.im) at hp
  change Bound (ConcretePadic318.place 17 (-ρ) (ConcretePadic318.negative_root 17 ρ hρ)) r (pair x.re x.im) at hn
  rw [Bound,ConcretePadic318.place_pair] at hp hn
  have hsum := bdiv Padic.addValuation (badd Padic.addValuation hp hn) two_value
  have hdiff := bdiv Padic.addValuation (bsub Padic.addValuation hp hn)
    (show Padic.addValuation (2*ρ)=0 by rw [Padic.addValuation.map_mul,two_value,root_value ρ hρ,zero_add])
  have hre : (((x.re:ℚ_[17])+(x.im:ℚ_[17])*ρ)+((x.re:ℚ_[17])+(x.im:ℚ_[17])*(-ρ)))/2=(x.re:ℚ_[17]) := by ring
  have him : (((x.re:ℚ_[17])+(x.im:ℚ_[17])*ρ)-((x.re:ℚ_[17])+(x.im:ℚ_[17])*(-ρ)))/(2*ρ)=(x.im:ℚ_[17]) := by
    field_simp [hρ0] <;> ring
  rw [hre] at hsum
  rw [him] at hdiff
  rw [PadicDetectorCoefficients318.rational_embedding,PadicDetectorCoefficients318.rational_embedding]
  exact ⟨hsum,hdiff⟩

/-- Uniform four-coordinate17-adic return bound for the literal oriented
chart. The initial modulus is20 and the unbounded factor is17^e. -/
theorem error_bound (e : ℕ) (m : ℤ) :
    ‖ActualOrbitLocalFilter318.error 17 (20*17^e*m)‖≤((17:ℝ)⁻¹)^e := by
  obtain ⟨ρ,hρ⟩ := ActualSeventeenEntry318.square_root_two
  have hp := place_precision ρ hρ e m
  have hn := place_precision (-ρ) (ConcretePadic318.negative_root 17 ρ hρ) e m
  have hu := recover_coefficients ρ hρ ((e:ℤ)+1) _ hp.1 hn.1
  have hv := recover_coefficients ρ hρ ((e:ℤ)+1) _ hp.2 hn.2
  have hle : (e:WithTop ℤ)≤(((e:ℤ)+1:ℤ):WithTop ℤ) := by exact_mod_cast (show (e:ℤ)≤e+1 by omega)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  fin_cases j
  · exact ActualOrbitLocalFilter318.norm_of_depth 17 e _ (le_trans hle hu.1)
  · exact ActualOrbitLocalFilter318.norm_of_depth 17 e _ (le_trans hle hu.2)
  · exact ActualOrbitLocalFilter318.norm_of_depth 17 e _ (le_trans hle hv.1)
  · exact ActualOrbitLocalFilter318.norm_of_depth 17 e _ (le_trans hle hv.2)

end SeventeenOrbitPrecision318
