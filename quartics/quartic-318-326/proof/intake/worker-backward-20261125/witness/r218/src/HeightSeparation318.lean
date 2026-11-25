module
public import ArithmeticSeparation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public section
namespace HeightSeparation318

noncomputable def heightConstant : ℝ := 2^5385

theorem heightConstant_ge_one : 1 ≤ heightConstant := by
  exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)

theorem eighty_height_lt : 80*heightConstant < (2:ℝ)^5392 := by
  have hp : (0:ℝ) < 2^5385 := by positivity
  calc
    80*heightConstant < 128*(2:ℝ)^5385 := by
      unfold heightConstant
      exact mul_lt_mul_of_pos_right (by norm_num) hp
    _ = (2:ℝ)^5392 := by rw [show 5392=7+5385 by omega, pow_add]; norm_num

/-- The exact 3-adic half-norm anchor implies a deliberately weakened binary
bound. The actual local anchor implication is not asserted here. -/
theorem anchor_binary_bound (c : ℝ) (hc : 2*3^32767 ≤ c) :
    (2:ℝ)^49151 < c := by
  have hp : (8:ℝ)^16383 < 9^16383 :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
  have hh : (2:ℝ)^49149 < 3^32766 := by
    calc
      (2:ℝ)^49149 = ((2:ℝ)^3)^16383 := by rw [←pow_mul]
      _ = (8:ℝ)^16383 := by norm_num
      _ < (9:ℝ)^16383 := hp
      _ = ((3:ℝ)^2)^16383 := by norm_num
      _ = (3:ℝ)^32766 := by rw [←pow_mul]
  have hhpos : (0:ℝ) < 2^49149 := by positivity
  have hstep : (2:ℝ)^49151 < 2*3^32767 := by
    calc
      (2:ℝ)^49151 = 4*(2:ℝ)^49149 := by
        rw [show 49151=2+49149 by omega, pow_add]; norm_num
      _ < 6*(2:ℝ)^49149 := mul_lt_mul_of_pos_right (by norm_num) hhpos
      _ < 6*(3:ℝ)^32766 := mul_lt_mul_of_pos_left hh (by norm_num)
      _ = 2*(3:ℝ)^32767 := by
        rw [show 32767=32766+1 by omega, pow_add, pow_one]; ring
  exact hstep.trans_le hc

/-- Fixed anchor dominates the ninth power needed for the order-13 defect. -/
theorem anchor_high_margin (c : ℝ) (hc : (2:ℝ)^49151 < c) :
    2*(80*heightConstant)^9 < c := by
  have hp : (80*heightConstant)^9 < ((2:ℝ)^5392)^9 :=
    pow_lt_pow_left₀ (eighty_height_lt) (by unfold heightConstant; positivity) (by norm_num)
  have htwo : (2:ℝ)^48529 < 2^49151 := by
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hid : 2*((2:ℝ)^5392)^9=(2:ℝ)^48529 := by
    rw [←pow_mul, show 48529=1+5392*9 by omega, pow_add]; norm_num
  calc
    2*(80*heightConstant)^9 < 2*((2:ℝ)^5392)^9 := mul_lt_mul_of_pos_left hp (by norm_num)
    _ = (2:ℝ)^48529 := hid
    _ < (2:ℝ)^49151 := htwo
    _ < c := hc

/-- Scalar index 8 versus contact exponent 49/8 leaves the exponent 15/64. -/
theorem anchor_scalar_margin (c : ℝ) (hc : (2:ℝ)^49151 < c) :
    80*heightConstant < c^((15:ℝ)/64) := by
  have hp : ((2:ℝ)^49151)^((15:ℝ)/64) < c^((15:ℝ)/64) :=
    Real.rpow_lt_rpow (by positivity) hc (by norm_num)
  have hl : (2:ℝ)^5392 < ((2:ℝ)^49151)^((15:ℝ)/64) := by
    rw [←Real.rpow_natCast, ←Real.rpow_natCast, ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  exact eighty_height_lt.trans (hl.trans hp)

/-- Numerical high-order contradiction, retaining its two actual height inputs. -/
theorem high_defect_impossible (H B D : ℝ) (hH : 1 ≤ H) (hB : 3 ≤ B)
    (hD0 : 0 ≤ D) (hD : D < 5*B^4)
    (hheight : B^2-6 < 7*H*D^((49:ℝ)/104)) :
    B^((3:ℝ)/26) < 80*H := by
  have hBp : 0 < B := by linarith
  have hHp : 0 < H := by linarith
  have ht := Real.rpow_lt_rpow hD0 hD (by norm_num : (0:ℝ)<49/104)
  rw [Real.mul_rpow (by norm_num) (by positivity),
    ←Real.rpow_natCast, ←Real.rpow_mul hBp.le] at ht
  norm_num only [Nat.cast_ofNat, show (4:ℝ)*(49/104)=49/26 by norm_num] at ht
  have hfive : (5:ℝ)^((49:ℝ)/104) ≤ 5 := by
    calc
      (5:ℝ)^((49:ℝ)/104) ≤ (5:ℝ)^(1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 5 := Real.rpow_one _
  have hpow : 1 ≤ B^((49:ℝ)/26) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hDb : D^((49:ℝ)/104) < 5*B^((49:ℝ)/26) :=
    ht.trans_le (mul_le_mul_of_nonneg_right hfive (by positivity))
  have hbound : B^2 < (80*H)*B^((49:ℝ)/26) := by
    nlinarith [mul_lt_mul_of_pos_left hDb (show 0<7*H by positivity)]
  have hid : B^2=B^((3:ℝ)/26)*B^((49:ℝ)/26) := by
    rw [←Real.rpow_add hBp, show (3:ℝ)/26+49/26=2 by norm_num, Real.rpow_two]
  rw [hid] at hbound
  exact (mul_lt_mul_iff_left₀ (by positivity : 0<B^((49:ℝ)/26))).mp hbound

/-- The order-4 numerator defect forces an upper logarithmic bound. -/
theorem low_defect_log_bound (H B N h : ℝ) (hH : 1 ≤ H) (hB : 3 ≤ B)
    (hh : 0 ≤ h) (hN0 : 0 ≤ N) (hN : N ≤ 2*Real.exp h*B)
    (hheight : B^2-6 < 7*H*N^((49:ℝ)/32)) :
    15*Real.log B < 32*Real.log (80*H)+49*h := by
  have hBp : 0 < B := by linarith
  have hHp : 0 < H := by linarith
  have ht := Real.rpow_le_rpow hN0 hN (by norm_num : (0:ℝ)≤49/32)
  rw [Real.mul_rpow (by positivity) hBp.le,
    Real.mul_rpow (by norm_num) (Real.exp_nonneg h), ←Real.exp_mul] at ht
  have htwo : (2:ℝ)^((49:ℝ)/32) ≤ 4 := by
    calc
      (2:ℝ)^((49:ℝ)/32) ≤ (2:ℝ)^(2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hpow : 1 ≤ B^((49:ℝ)/32) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hexp : 1 ≤ Real.exp (h*(49/32)) := Real.one_le_exp (by positivity)
  have hNb : N^((49:ℝ)/32) ≤ 4*Real.exp (h*(49/32))*B^((49:ℝ)/32) := by
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity))
  have hprod : 1 ≤ Real.exp (h*(49/32))*B^((49:ℝ)/32) :=
    one_le_mul_of_one_le_of_one_le hexp hpow
  have hbound : B^2 < (80*H*Real.exp (h*(49/32)))*B^((49:ℝ)/32) := by
    nlinarith [mul_le_mul_of_nonneg_left hNb (show 0≤7*H by positivity)]
  have hid : B^2=B^((15:ℝ)/32)*B^((49:ℝ)/32) := by
    rw [←Real.rpow_add hBp, show (15:ℝ)/32+49/32=2 by norm_num, Real.rpow_two]
  rw [hid] at hbound
  have hquot := (mul_lt_mul_iff_left₀ (by positivity : 0<B^((49:ℝ)/32))).mp hbound
  have hlog := Real.log_lt_log (by positivity : 0<B^((15:ℝ)/32)) hquot
  rw [Real.log_rpow hBp, Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
  linarith

/-- The scalar radical and index bound produce the exact linear height margin. -/
theorem scalar_height_small (H c h : ℝ) (hc : 0<c)
    (hmargin : 80*H<c^((15:ℝ)/64))
    (hheight : h≤H*c^((49:ℝ)/64)) : h<c/80 := by
  have ht := mul_lt_mul_of_pos_right hmargin
    (Real.rpow_pos_of_pos hc ((49:ℝ)/64))
  have hid : c^((15:ℝ)/64)*c^((49:ℝ)/64)=c := by
    rw [←Real.rpow_add hc, show (15:ℝ)/64+49/64=1 by norm_num, Real.rpow_one]
  rw [hid] at ht
  nlinarith

/-- Lucas growth excludes every nonzero numerator defect with these margins. -/
theorem low_defect_contradiction (H B N c h : ℝ) (hH : 1≤H) (hB : 3≤B)
    (hh : 0≤h) (hN0 : 0≤N) (hN : N≤2*Real.exp h*B)
    (hheight : B^2-6<7*H*N^((49:ℝ)/32))
    (hc : 8≤c) (hlogH : Real.log (80*H)<c/80)
    (hscalar : h<c/80) (hlucas : c-4<Real.log B) : False := by
  have hl := low_defect_log_bound H B N h hH hB hh hN0 hN hheight
  linarith

/-- The fixed coefficient also supplies the logarithmic margin used in the low comparison. -/
theorem anchor_log_margin (c : ℝ) (hc : (2:ℝ)^49151<c) :
    Real.log (80*heightConstant)<c/80 := by
  have hHp : 0<80*heightConstant := by unfold heightConstant; positivity
  have hl := Real.log_lt_log hHp eighty_height_lt
  rw [Real.log_pow] at hl
  have hlogtwo : Real.log (2:ℝ)<1 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1) using 1 <;> norm_num
  have hcut : (2:ℝ)^19 ≤ 2^49151 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hcut
  have hc' : (524288:ℝ)<c := hcut.trans_lt hc
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hc', hl, hlogtwo]

/-- The ninth-power margin contradicts the explicit order-13 bound. -/
theorem high_defect_contradiction (H B D c : ℝ) (hH : 1≤H) (hB : 3≤B)
    (hD0 : 0≤D) (hD : D<5*B^4)
    (hheight : B^2-6<7*H*D^((49:ℝ)/104))
    (hanchor : 2*(80*H)^9<c) (hcB : c≤B+1) : False := by
  have hX : 1<80*H := by linarith
  have hX9 : 1≤(80*H)^9 := one_le_pow₀ hX.le
  have hbase : (80*H)^9<B := by linarith
  have hpow := Real.rpow_lt_rpow (by positivity : 0≤(80*H)^9) hbase
    (by norm_num : (0:ℝ)<3/26)
  rw [←Real.rpow_natCast, ←Real.rpow_mul (by positivity : 0≤80*H)] at hpow
  have hgreater : 80*H < (80*H)^((9:ℝ)*(3/26)) := by
    calc
      80*H = (80*H)^(1:ℝ) := (Real.rpow_one _).symm
      _ < (80*H)^((9:ℝ)*(3/26)) :=
        Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
  exact (not_lt_of_ge (high_defect_impossible H B D hH hB hD0 hD hheight).le)
    (hgreater.trans hpow)

/-- This constructs a genuine odd-label certificate from the numerical low
separation argument. The height-transfer, Lucas growth and parity inputs are
explicit; they still have to be proved for actual source assignments. -/
noncomputable def odd_certificate_from_height_data (beta : ℚ) (n : ℤ)
    (B c h : ℝ) (hn : Odd n) (hB : 3≤B) (hh : 0≤h)
    (hanchor : (2:ℝ)^49151<c) (hc : 8≤c)
    (hscalar : h≤heightConstant*c^((49:ℝ)/64))
    (hlucas : c-4<Real.log B)
    (hnum : ((beta-n).num.natAbs : ℝ)≤2*Real.exp h*B)
    (hheight : beta≠n → B^2-6<7*heightConstant*
      (((beta-n).num.natAbs : ℝ)^((49:ℝ)/32))) :
    ArithmeticSeparation.OddLabelSeparation beta := by
  have heq : beta=n := by
    by_contra hnq
    have hcp : 0<c := lt_of_lt_of_le (by norm_num : (0:ℝ)<8) hc
    exact low_defect_contradiction heightConstant B
      ((beta-n).num.natAbs : ℝ) c h heightConstant_ge_one hB hh (by positivity)
      hnum (hheight hnq) hc (anchor_log_margin c hanchor)
      (scalar_height_small heightConstant c h hcp (anchor_scalar_margin c hanchor) hscalar)
      hlucas
  exact {
    label := n
    modulus := 1
    divides := by simp [heq]
    small := by simp [heq]
    odd := hn
  }

/-- The odd-affine input is now integral once the displayed height data are supplied. -/
theorem odd_affine_integral_from_height_data (q : ℚ) (n : ℤ)
    (B c h : ℝ) (hn : Odd n) (hB : 3≤B) (hh : 0≤h)
    (hanchor : (2:ℝ)^49151<c) (hc : 8≤c)
    (hscalar : h≤heightConstant*c^((49:ℝ)/64))
    (hlucas : c-4<Real.log B)
    (hnum : ((3723*(2*q+1)^2-n).num.natAbs : ℝ)≤2*Real.exp h*B)
    (hheight : 3723*(2*q+1)^2≠n → B^2-6<7*heightConstant*
      (((3723*(2*q+1)^2-n).num.natAbs : ℝ)^((49:ℝ)/32))) :
    ∃ z : ℤ, (z : ℚ)=q :=
  ArithmeticSeparation.odd_affine_input q
    (odd_certificate_from_height_data _ n B c h hn hB hh hanchor hc hscalar hlucas hnum hheight)

/-- Both Kummer orientations give the same scalar-to-Lucas size comparison. -/
theorem scalar_orientation_bounds (a c : ℝ)
    (hc : c=|a-1| ∨ c=|a+1|) : c≤|a|+1 ∧ |a|≤c+1 := by
  rcases hc with rfl | rfl
  · have h1 := abs_sub a 1
    have h2 := abs_add_le (a-1) 1
    norm_num only [abs_one, sub_add_cancel] at *
    exact ⟨h1, h2⟩
  · have h1 := abs_add_le a 1
    have h2 := abs_sub (a+1) 1
    norm_num only [abs_one, add_sub_cancel_right] at *
    exact ⟨h1, h2⟩

/-- Adic parity bookkeeping: no nonnegative label valuation can hide in the sum. -/
theorem parity_from_norm_anchor (v : Fin 4 → ℤ)
    (hv : ∀i, 0≤v i) (hanchor : 0≤ -2*(∑i,v i)) : ∀i,v i=0 := by
  have hs : (∑i,v i)=0 := by
    have hnonneg : 0≤∑i,v i := Finset.sum_nonneg (fun i _ => hv i)
    linarith
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hv i)).mp hs i (Finset.mem_univ i)

/-- The input cannot hit the two positive finite exceptional contacts. -/
theorem input_not_positive_contact (q : ℚ) (m : ℤ) (hm0 : 0<m) (hm : m<3723) :
    3723*(2*q+1)^2 ≠ (m:ℚ) := by
  intro heq
  obtain ⟨z,hz⟩ := QuarticOptimization.squarefree_multiple_square_integral
    (2*q+1) 3723 OddAffineInput.multiplier_3723_squarefree m heq
  have hi : 3723*z^2=m := by
    rw [←hz] at heq
    exact_mod_cast heq
  have hz0 : z≠0 := by intro hh; simp [hh] at hi; omega
  have hsq : 1≤z^2 := by have := sq_pos_of_ne_zero hz0; omega
  nlinarith

theorem input_height_domain (q : ℚ) :
    3723*(2*q+1)^2 ≠ 1 ∧ 3723*(2*q+1)^2 ≠ 2401 ∧
    3723*(2*q+1)^2 ≠ -(343:ℚ)/32 := by
  refine ⟨?_,?_,?_⟩
  · simpa using input_not_positive_contact q 1 (by norm_num) (by norm_num)
  · simpa using input_not_positive_contact q 2401 (by norm_num) (by norm_num)
  · have hq := sq_nonneg (2*q+1)
    intro h
    linarith

/-- The beta=0 branch is precisely q=-1/2; it is not silently discarded. -/
theorem input_zero_iff (q : ℚ) : 3723*(2*q+1)^2=0 ↔ q=-(1:ℚ)/2 := by
  constructor
  · intro h
    have hs : (2*q+1)^2=0 := by linarith
    have hlin : 2*q+1=0 := sq_eq_zero_iff.mp hs
    linarith
  · intro h
    rw [h]
    norm_num

/-- The radical-to-index transfer uses the actual scalar index eight. -/
theorem scalar_radical_height (H M c h : ℝ) (hH : 0≤H) (hM : 0≤M)
    (hdiv : M^8≤c) (hheight : h≤H*M^((49:ℝ)/8)) :
    h≤H*c^((49:ℝ)/64) := by
  have ht := Real.rpow_le_rpow (by positivity : 0≤M^8) hdiv
    (by norm_num : (0:ℝ)≤49/64)
  rw [←Real.rpow_natCast, ←Real.rpow_mul hM] at ht
  norm_num only [Nat.cast_ofNat, show (8:ℝ)*(49/64)=49/8 by norm_num] at ht
  exact hheight.trans (mul_le_mul_of_nonneg_left ht hH)

/-- The exact bad-prime product is below the binary budget used for H. -/
theorem bad_prime_product_bound :
    (11185621387570686764517810:ℕ)<2^84 := by norm_num

theorem conductor_constant_bound : (210:ℝ)^300<(2:ℝ)^2400 := by
  have hp : (210:ℝ)^300<256^300 :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
  calc
    (210:ℝ)^300 < (256:ℝ)^300 := hp
    _ = ((2:ℝ)^8)^300 := by norm_num
    _ = (2:ℝ)^2400 := by rw [←pow_mul]

/-- Absorb the complete geometric coefficient and additive 128 into the exact
proof constant. This proves arithmetic only, not the preceding height theorem. -/
theorem height_constant_absorption (C Bad M h : ℝ)
    (hC0 : 0≤C) (hC : C≤(2:ℝ)^2400)
    (hBad0 : 0≤Bad) (hBad : Bad≤(2:ℝ)^84) (hM : 1≤M)
    (hh : h<2^68*C^2*(Bad*M)^((49:ℝ)/8)+128) :
    h<heightConstant*M^((49:ℝ)/8) := by
  have hMp : 0<M := by linarith
  have hC2 : C^2≤(2:ℝ)^4800 := by
    calc
      C^2 ≤ ((2:ℝ)^2400)^2 := pow_le_pow_left₀ hC0 hC 2
      _ = (2:ℝ)^4800 := by rw [←pow_mul]
  have hBadPow : Bad^((49:ℝ)/8)≤(2:ℝ)^515 := by
    calc
      Bad^((49:ℝ)/8) ≤ ((2:ℝ)^84)^((49:ℝ)/8) :=
        Real.rpow_le_rpow hBad0 hBad (by norm_num)
      _ = (2:ℝ)^((84:ℝ)*(49/8)) := by
        rw [←Real.rpow_natCast, ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
        norm_num only [Nat.cast_ofNat]
      _ ≤ (2:ℝ)^(515:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = (2:ℝ)^515 := Real.rpow_natCast _ _
  have hcoeff : 2^68*C^2*Bad^((49:ℝ)/8)≤(2:ℝ)^5383 := by
    calc
      2^68*C^2*Bad^((49:ℝ)/8) ≤
        2^68*(2:ℝ)^4800*(2:ℝ)^515 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC2 (by positivity)) hBadPow
            (by positivity) (by positivity)
      _ = (2:ℝ)^5383 := by rw [←pow_add, ←pow_add]
  have hMPow : 1≤M^((49:ℝ)/8) := Real.one_le_rpow hM (by norm_num)
  have h128 : (128:ℝ)≤2^5383 := by
    calc
      (128:ℝ) = (2:ℝ)^7 := by norm_num
      _ ≤ (2:ℝ)^5383 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h128M : (128:ℝ)≤2^5383*M^((49:ℝ)/8) :=
    h128.trans (le_mul_of_one_le_right (by positivity) hMPow)
  rw [Real.mul_rpow hBad0 hMp.le, ←mul_assoc] at hh
  have hfirst : h<(2:ℝ)^5383*M^((49:ℝ)/8)+128 :=
    hh.trans_le (by
      have hm := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hMp.le ((49:ℝ)/8))
      linarith only [hm])
  calc
    h < (2:ℝ)^5383*M^((49:ℝ)/8)+128 := hfirst
    _ ≤ (2:ℝ)^5383*M^((49:ℝ)/8)+(2:ℝ)^5383*M^((49:ℝ)/8) :=
      by linarith only [h128M]
    _ = (2:ℝ)^5384*M^((49:ℝ)/8) := by
      rw [show 5384=5383+1 by omega,pow_add,pow_one]; ring
    _ ≤ heightConstant*M^((49:ℝ)/8) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)

end HeightSeparation318
