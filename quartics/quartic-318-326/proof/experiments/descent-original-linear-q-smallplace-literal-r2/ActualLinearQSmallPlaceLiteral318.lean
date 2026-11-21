module
public import ActualLinearQFoldedDenominator318
public section
noncomputable section
namespace ActualLinearQSmallPlaceLiteral318

open scoped BigOperators
open ActualLinearQArithmeticCalibration318 ActualLinearQLiteralFoldCalibration318
open ActualLinearQFoldedDenominator318

private theorem near_one_value (v : AddValuation ℚ (WithTop ℤ)) (x : ℚ)
    (h : 0 < v (x-1)) : v x = 0 := by
  simpa using v.map_eq_of_lt_sub (x:=1) (y:=x) (by simpa using h)

private theorem add_positive (v : AddValuation ℚ (WithTop ℤ)) (x y : ℚ)
    (hx : 0 < v x) (hy : 0 < v y) : 0 < v (x+y) :=
  lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)

private theorem mul_pos_of_right (v : AddValuation ℚ (WithTop ℤ)) (x y : ℚ)
    (hx : 0 < v x) (hy : 0 ≤ v y) : 0 < v (x*y) := by
  rw [v.map_mul]
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy)

private theorem halo_square (v : AddValuation ℚ (WithTop ℤ)) (x : ℚ)
    (hx : 0 < v (x-1)) : 0 < v (x^2-1) := by
  have h := near_one_value v x hx
  have ha : 0 ≤ v (x+1) := by simpa [h] using v.map_add x 1
  rw [show x^2-1=(x-1)*(x+1) by ring]
  exact mul_pos_of_right v _ _ hx ha

/-- The norm is a local unit, but the trace divisor contributes the
actual valuation of 2. In particular the dyadic result is not a unit. -/
theorem trace_of_near (p : ℕ) [Fact p.Prime] (x : ℚ × ℚ)
    (h2 : 0 ≤ val p (2:ℚ)) (hx : 0 < val p (x.1-1) ∧ 0 < val p x.2) :
    trace x ≠ 0 ∧ padicValRat p (trace x) = -padicValRat p (2:ℚ) := by
  let v := val p
  have ha := near_one_value v x.1 hx.1
  have ha0 : x.1 ≠ 0 := (v.ne_top_iff).mp (by rw [ha]; simp)
  have hb : 0 < v (2*x.2^2) := by
    rw [mul_comm (2:ℚ),pow_two]
    exact mul_pos_of_right v _ _ (mul_pos_of_right v _ _ hx.2 hx.2.le) h2
  have hn := add_positive v (x.1^2-1) (-(2*x.2^2))
    (halo_square v x.1 hx.1) (by simpa only [v.map_neg] using hb)
  have hn' : 0 < v ((x.1^2-2*x.2^2)-1) := by
    rw [show (x.1^2-2*x.2^2)-1=(x.1^2-1)+(-(2*x.2^2)) by ring]
    exact hn
  have hN := near_one_value v _ hn'
  have hN0 : x.1^2-2*x.2^2 ≠ 0 := (v.ne_top_iff).mp (by rw [hN]; simp)
  have hτ : trace x ≠ 0 := div_ne_zero hN0 (mul_ne_zero (by decide) ha0)
  have hvA : padicValRat p x.1 = 0 := by
    rw [val_rat p _ ha0] at ha
    exact_mod_cast ha
  have hvN : padicValRat p (x.1^2-2*x.2^2) = 0 := by
    rw [val_rat p _ hN0] at hN
    exact_mod_cast hN
  refine ⟨hτ,?_⟩
  rw [trace,padicValRat.div hN0 (mul_ne_zero (by decide) ha0),
    padicValRat.mul (by decide : (2:ℚ) ≠ 0) ha0,hvN,hvA,add_zero,zero_sub]

variable (p : ℕ) [Fact p.Prime]

private theorem two_nonneg : 0 ≤ val p (2:ℚ) := by
  rw [val_rat p _ (by decide), show (2:ℚ) = (2:ℕ) by norm_num, padicValRat.of_nat]
  have hn : (0:ℤ) ≤ (padicValNat p 2:ℤ) := Nat.cast_nonneg _
  exact_mod_cast hn

/-- Dyadic normalization has depth −1, not zero. -/
theorem trace_two [Fact (Nat.Prime 2)] (x : ℚ × ℚ)
    (hx : 0 < val 2 (x.1-1) ∧ 0 < val 2 x.2) :
    trace x ≠ 0 ∧ padicValRat 2 (trace x) = -1 := by
  have h := trace_of_near 2 x (two_nonneg 2) hx
  have hTwo : padicValRat 2 (2:ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using
      (padicValRat.self (p:=2) (by decide : 1 < (2:ℕ)))
  simpa only [hTwo] using h

private theorem val_product {I : Type*} (S : Finset I) (f : I → ℚ)
    (hf : ∀ i∈S,f i≠0) :
    padicValRat p (∏ i∈S,f i)=∑ i∈S,padicValRat p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,padicValRat.one]
  | insert a S ha ih =>
    have h₁ : f a≠0 := hf a (Finset.mem_insert_self _ _)
    have hs : ∀ i∈S,f i≠0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,
      padicValRat.mul h₁ (Finset.prod_ne_zero_iff.mpr hs),ih hs]

private theorem weighted_positive (x y : ℚ) (B : ℤ) (hx : x ≠ 0)
    (hxv : -B < padicValRat p x) (hy : (B:WithTop ℤ) ≤ val p y) :
    0 < val p (x*y) := by
  have hZ : 0 < padicValRat p x+B := by omega
  rw [(val p).map_mul,val_rat p _ hx]
  have h1 : (0:WithTop ℤ) < ((padicValRat p x:WithTop ℤ)+(B:WithTop ℤ)) := by
    rw [←WithTop.coe_add]
    exact_mod_cast hZ
  exact h1.trans_le (add_le_add (le_refl _) hy)

/-- Complete small-prime computation on the actual sixteen coefficients
and the original five contact factors, with an exact dyadic correction.
The lower coefficient envelope may include zeros; the five factors
are supplied with their actual local unit values and are not changed. -/
theorem folded_small_value (w : ℕ → ℚ) (c u A q : ℚ)
    (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0) (hq : q ≠ 0)
    (huv : padicValRat p u = 0) (hqv : padicValRat p q = 0)
    (hdeep : padicValRat p c < padicValRat p A)
    (n : Fin 5 → ℚ) (hn : ∀ i,n i ≠ 0) (hnu : ∀ i,padicValRat p (n i) = 0)
    (hPr : factorProduct c u A q = ∏ i : Fin 5,n i)
    (B : ℤ) (hCoeff : ∀ e ∈ coefficients w, (B : WithTop ℤ) ≤ val p e.2.1 ∧
      (B : WithTop ℤ) ≤ val p e.2.2)
    (hdepth : ∀ e ∈ ({4,64,244}:Finset ℤ),
      -B < 6*padicValRat p A+e*padicValRat p c) :
    trace (fold w c u A q) ≠ 0 ∧ delta c u A q ≠ 0 ∧
      padicValRat p (trace (fold w c u A q)) = -padicValRat p (2:ℚ) ∧
      padicValRat p (rootFactor (trace (fold w c u A q)) c u A q) =
        padicValRat p A-6*padicValRat p c-padicValRat p (2:ℚ) ∧
      padicValRat p (pole (trace (fold w c u A q)) c u A q) =
        2*(padicValRat p A-6*padicValRat p c-padicValRat p (2:ℚ)) := by
  let T := parameter c u A q
  have hDe : A^2*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hA) hq
  have hT : T ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero hu hDe)
  have hTv : padicValRat p T=2*padicValRat p c-2*padicValRat p A := by
    dsimp only [T,parameter,time]
    rw [padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero hu hDe),
      padicValRat.div hu hDe,padicValRat.mul (pow_ne_zero _ hA) hq,
      padicValRat.pow,padicValRat.pow,huv,hqv] <;> norm_num <;> ring
  have hΔ : delta c u A q ≠ 0 := by
    intro h
    have he : T=1 := sub_eq_zero.mp h
    rw [he,padicValRat.one] at hTv
    omega
  have hΔv : padicValRat p (delta c u A q)=2*padicValRat p c-2*padicValRat p A := by
    have hs : T+(-1) ≠ 0 := by simpa only [T,delta,sub_eq_add_neg] using hΔ
    have hsmall : padicValRat p T < padicValRat p (-1) := by
      rw [padicValRat.neg,padicValRat.one,hTv]
      omega
    exact (by simpa only [T,delta,sub_eq_add_neg] using
      (padicValRat.add_eq_of_lt hs hT (by decide) hsmall).trans hTv)
  have hNP : factorProduct c u A q ≠ 0 := by
    rw [hPr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hNPv : padicValRat p (factorProduct c u A q)=0 := by
    rw [hPr,val_product p _ _ (fun i _ => hn i)]
    simp only [hnu,Finset.sum_const_zero]
  have hF : contact T ≠ 0 := by
    dsimp only [T]
    rw [contact_product c u A q hc hA hq]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hDe)) hNP
  have hFv : padicValRat p (contact T)=10*padicValRat p c-10*padicValRat p A := by
    dsimp only [T]
    rw [contact_product c u A q hc hA hq,
      padicValRat.mul (div_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hDe)) hNP,
      padicValRat.div (pow_ne_zero _ hc) (pow_ne_zero _ hDe),
      padicValRat.pow,padicValRat.pow,padicValRat.mul (pow_ne_zero _ hA) hq,
      padicValRat.pow,hNPv,hqv] <;> norm_num <;> ring
  have hW : weight c u A q ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF)
  have hWv : padicValRat p (weight c u A q)=6*padicValRat p A+4*padicValRat p c := by
    rw [weight,padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF),
      padicValRat.div (pow_ne_zero _ hΔ) hF,padicValRat.pow,padicValRat.pow,hΔv,hFv] <;> norm_num <;> ring
  have hw (i : Fin 3) : weights c u A q i ≠ 0 ∧ -B < padicValRat p (weights c u A q i) := by
    fin_cases i
    · exact ⟨hW,by rw [hWv]; exact hdepth 4 (by decide)⟩
    · refine ⟨mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),?_⟩
      change -B < padicValRat p ((weight c u A q)^7*(delta c u A q)^18)
      rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
        padicValRat.pow,padicValRat.pow,hWv,hΔv]
      linarith only [hdepth 64 (by decide)]
    · refine ⟨mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),?_⟩
      change -B < padicValRat p ((weight c u A q)^25*(delta c u A q)^72)
      rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
        padicValRat.pow,padicValRat.pow,hWv,hΔv]
      linarith only [hdepth 244 (by decide)]
  have hFold : 0 < val p ((fold w c u A q).1-1) ∧ 0 < val p (fold w c u A q).2 := by
    unfold fold
    apply folded_near (val p) (two_nonneg p) _ (1,0) (by simp)
    intro e he
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp he
    exact ⟨weighted_positive p _ _ B (hw m.1).1 (hw m.1).2 (hCoeff m hm).1,
      weighted_positive p _ _ B (hw m.1).1 (hw m.1).2 (hCoeff m hm).2⟩
  obtain ⟨hτ,hτv⟩ := trace_of_near p _ (two_nonneg p) hFold
  let τ := trace (fold w c u A q)
  have hRD : A^5*q^3*(delta c u A q)^3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hq)) (pow_ne_zero _ hΔ)
  have hz : rootFactor τ c u A q ≠ 0 := div_ne_zero hτ hRD
  have hzv : padicValRat p (rootFactor τ c u A q) =
      padicValRat p A-6*padicValRat p c-padicValRat p (2:ℚ) := by
    change padicValRat p (rootFactor (trace (fold w c u A q)) c u A q) = _
    rw [rootFactor,padicValRat.div hτ hRD,
      padicValRat.mul (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hq)) (pow_ne_zero _ hΔ),
      padicValRat.mul (pow_ne_zero _ hA) (pow_ne_zero _ hq),
      padicValRat.pow,padicValRat.pow,padicValRat.pow,hτv,hqv,hΔv] <;> norm_num <;> ring
  refine ⟨hτ,hΔ,hτv,hzv,?_⟩
  have hP : pole τ c u A q=q*factorProduct c u A q*(rootFactor τ c u A q)^2 :=
    pole_squareclass τ c u A q hc hA hq hΔ
  change padicValRat p (pole τ c u A q) = _
  rw [hP,padicValRat.mul (mul_ne_zero hq hNP) (pow_ne_zero _ hz),
    padicValRat.mul hq hNP,padicValRat.pow,hqv,hNPv,hzv] <;> norm_num <;> ring

/-- The common preselected scale budget absorbs the exact dyadic
correction; no uniform bound on the detector coefficients is inserted. -/
theorem small_profile (w : ℕ → ℚ) (c u A q : ℚ)
    (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0) (hq : q ≠ 0)
    (huv : padicValRat p u = 0) (hqv : padicValRat p q = 0)
    (n : Fin 5 → ℚ) (hn : ∀ i,n i ≠ 0) (hnu : ∀ i,padicValRat p (n i) = 0)
    (hPr : factorProduct c u A q = ∏ i : Fin 5,n i)
    (hsq : IsSquare (q:ℚ_[p])) (hsk : ∀ i,IsSquare (n i:ℚ_[p]))
    (B m : ℤ) (hm : 0 ≤ m)
    (hCoeff : ∀ e ∈ coefficients w, (B : WithTop ℤ) ≤ val p e.2.1 ∧
      (B : WithTop ℤ) ≤ val p e.2.2)
    (hAdeep : |B| + 244*|padicValRat p c| + |padicValRat p (2:ℚ)| + m+1 ≤ padicValRat p A) :
    let b := pole (trace (fold w c u A q)) c u A q
    IsSquare (b:ℚ_[p]) ∧ m ≤ padicValRat p b := by
  have hBa := neg_le_abs B
  have hc₁ := le_abs_self (padicValRat p c)
  have hc₂ := neg_le_abs (padicValRat p c)
  have h2a := le_abs_self (padicValRat p (2:ℚ))
  have hab := abs_nonneg B
  have hac := abs_nonneg (padicValRat p c)
  have ha2 := abs_nonneg (padicValRat p (2:ℚ))
  obtain ⟨_,hΔ,_,_,hv⟩ := folded_small_value p w c u A q hc hu hA hq huv hqv
    (by omega) n hn hnu hPr B hCoeff (by
      intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl|rfl|rfl <;> omega)
  dsimp only
  refine ⟨?_,?_⟩
  · simp only [pole_squareclass _ c u A q hc hA hq hΔ,Rat.cast_mul,Rat.cast_pow]
    have hPN : IsSquare (factorProduct c u A q:ℚ_[p]) := by
      rw [hPr]
      simpa [Fin.prod_univ_succ,Rat.cast_mul,mul_assoc] using
        ((((hsk 0).mul (hsk 1)).mul (hsk 2)).mul (hsk 3)).mul (hsk 4)
    exact (hsq.mul hPN).mul
      ⟨(rootFactor (trace (fold w c u A q)) c u A q:ℚ_[p]),by
        simp only [rootFactor,pow_two]⟩
  · rw [hv]
    omega

end ActualLinearQSmallPlaceLiteral318
