module
public import ActualPreparedPoleTwoAdic318
public section
noncomputable section
namespace ActualPreparedPoleResidues318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleLocalSquares318
open ActualPreparedPoleMutualRoots318 ActualPreparedPoleTwoAdic318
open ActualTwoDescentLocalValuationTools318

/-- A local square multiple of integral3-adic units preserves the actual
residue modulo3, through the integral residue map. -/
theorem mod3_of_square_multiple (a t : ℕ) (ha : ¬3∣a) (ht : ¬3∣t)
    (r : ℚ_[3]) (hf : (a:ℚ_[3])=(t:ℚ_[3])*r^2) :
    (a:ZMod 3)=(t:ZMod 3) := by
  have ha0 : a≠0 := by intro he; apply ha; rw [he]; exact dvd_zero _
  have ht0 : t≠0 := by intro he; apply ht; rw [he]; exact dvd_zero _
  have hac : (a:ℚ_[3])≠0 := Nat.cast_ne_zero.mpr ha0
  have htc : (t:ℚ_[3])≠0 := Nat.cast_ne_zero.mpr ht0
  have hr0 : r≠0 := by
    intro he
    apply hac
    simpa only [he,zero_pow (by decide : (2:ℕ)≠0),mul_zero] using hf
  have va := actual_prime_unit_valuation (p:=3) a ha
  have vt := actual_prime_unit_valuation (p:=3) t ht
  have hv := congrArg Padic.valuation hf
  rw [Padic.valuation_mul htc (pow_ne_zero 2 hr0),Padic.valuation_pow,va,vt] at hv
  have vr : r.valuation=0 := by omega
  have hn := actual_norm_one_of_valuation_zero r hr0 vr
  let R : ℤ_[3] := ⟨r,hn.le⟩
  have uR : IsUnit R := PadicInt.isUnit_iff.mpr hn
  have he : (a:ℤ_[3])=(t:ℤ_[3])*R^2 := by
    apply Subtype.ext
    exact hf
  have hm := congrArg PadicInt.toZMod he
  simp only [map_mul,map_pow,map_natCast] at hm
  have hz : PadicInt.toZMod R≠0 := (uR.map PadicInt.toZMod).ne_zero
  have hs : ∀ z : ZMod 3, z≠0 → z^2=1 := by decide
  simpa only [hs _ hz,mul_one] using hm

/-- The actual beta has unit squareclass17 at3, not the square class1. -/
theorem beta_mod3 {b : ℚ} (C : Classes b) (H : Preparation b) :
    (C.beta:ZMod 3)=2 := by
  obtain ⟨v,hv⟩ := H.square_three
  have hv' : v^2=(b:ℚ_[3]) := by simpa only [pow_two] using hv.symm
  have hc : (C.c:ℚ_[3])≠0 := Rat.cast_ne_zero.mpr C.c_ne
  have hf : (17:ℚ_[3])*(b:ℚ_[3])=(C.beta:ℚ_[3])*(C.c:ℚ_[3])^2 := by
    exact_mod_cast C.first_class
  have he : (C.beta:ℚ_[3])=(17:ℚ_[3])*(v/(C.c:ℚ_[3]))^2 := by
    calc
      (C.beta:ℚ_[3])=((C.beta:ℚ_[3])*(C.c:ℚ_[3])^2)/(C.c:ℚ_[3])^2 :=
        (mul_div_cancel_right₀ _ (pow_ne_zero 2 hc)).symm
      _=((17:ℚ_[3])*(b:ℚ_[3]))/(C.c:ℚ_[3])^2 := by rw [hf]
      _=(17:ℚ_[3])*(v/(C.c:ℚ_[3]))^2 := by rw [div_pow,hv']; ring
  have hm := mod3_of_square_multiple C.beta 17 (avoid_two_three C H).2.1
    (by decide) _ he
  simpa using hm

/-- Depth at3 produces an actual theta root in the odd-prime Hensel
neighborhood, so the same theta is1 modulo3. -/
theorem theta_mod3 {b : ℚ} (C : Classes b) (H : Preparation b) :
    (C.theta:ZMod 3)=1 := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hb0 : (b:ℚ_[3])≠0 := Rat.cast_ne_zero.mpr (ne_of_gt H.positive)
  have h17 : (17:ℚ_[3])≠0 := by norm_num
  have hv : (17:ℚ_[3]).valuation<(b:ℚ_[3]).valuation := by
    rw [show (b:ℚ_[3]).valuation=padicValRat 3 b from Padic.valuation_ratCast,
      show (17:ℚ_[3])=((17:ℕ):ℚ_[3]) from rfl,
      Padic.valuation_natCast,padicValNat_primes (by decide : 3≠17)]
    have hh := H.depth_three
    omega
  obtain ⟨r,_,hr⟩ := theta_at_small_pole (by decide : 3≠2) C
    (ActualTwoDescentCloseSquare318.actual_small_ratio _ _ hb0 h17 hv)
  have hm := mod3_of_square_multiple C.theta 1 (avoid_two_three C H).2.2.2
    (by decide) r (by simpa only [one_mul] using hr.symm)
  simpa only [Nat.cast_one] using hm

/-- The literal prepared squarefree coefficients satisfy the exact
mod24 inputs of the existing simultaneous-descent producer. -/
theorem coefficients_mod24 {b : ℚ} (C : Classes b) (H : Preparation b) :
    (C.beta:ZMod 24)=17 ∧ (C.theta:ZMod 24)=1 := by
  obtain ⟨hB8,hT8⟩ := coefficients_mod8 C H
  have hB3 := beta_mod3 C H
  have hT3 := theta_mod3 C H
  have b8 : C.beta%8=1 := by simpa using congrArg ZMod.val hB8
  have t8 : C.theta%8=1 := by simpa using congrArg ZMod.val hT8
  have b3 : C.beta%3=2 := by simpa using congrArg ZMod.val hB3
  have t3 : C.theta%3=1 := by simpa using congrArg ZMod.val hT3
  constructor
  · have he : C.beta%24=17 := by omega
    apply ZMod.val_injective
    simpa using he
  · have he : C.theta%24=1 := by omega
    apply ZMod.val_injective
    simpa using he

end ActualPreparedPoleResidues318
