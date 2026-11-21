module
public import ActualA4CRTResidueProduct318
public section
noncomputable section
namespace ActualA4MediumCRTError318

open scoped BigOperators
open ActualA4IntegerBoxFibres318 ActualA4CRTResidueProduct318

@[expose] def density (d : ℕ) (D : Finset (Vec (ZMod d))) : ℝ :=
  (D.card:ℝ)/(d:ℝ)^4

/-- ACTUAL finite A4 sieve remainder with no angular or analytic error.
The count is the intersection of BOTH true masks at the same point.
The main denominator is ell^4, even when d=1; no field-uniform count
or Gaussian generator independence is used. -/
theorem medium_error (l d B : ℕ) (hl : 0 < l) (hd : 0 < d) (hB : 1 ≤ B)
    (hC : Nat.Coprime l d) (hRange : l*d ≤ B)
    (Ω : Finset (Vec (ZMod l))) (D : Finset (Vec (ZMod d)))
    (hΩ : Ω.card ≤ 4*l^2) :
    |((accepted (l*d) B (joint hC Ω D)).card:ℝ)-
       ((2*B+1:ℕ):ℝ)^4*((Ω.card:ℝ)/(l:ℝ)^4)*density d D|
       ≤ 1620*(B:ℝ)^3*(d:ℝ)/(l:ℝ) := by
  letI : NeZero d := ⟨hd.ne'⟩
  letI : NeZero (l*d) := ⟨Nat.ne_of_gt (Nat.mul_pos hl hd)⟩
  have hdl : 0 < (d:ℝ) := by exact_mod_cast hd
  have hll : 0 < (l:ℝ) := by exact_mod_cast hl
  have hB' : 1 ≤ (B:ℝ) := by exact_mod_cast hB
  have hden : 0 < (l:ℝ)*(d:ℝ) := mul_pos hll hdl
  have hLen : l*d ≤ 2*B+1 := by omega
  have hD : D.card ≤ d^4 := by
    have h := Finset.card_le_card (Finset.subset_univ D)
    simpa only [Finset.card_univ,Fintype.card_fun,ZMod.card,Fintype.card_fin] using h
  let L : ℝ := ((2*B+1:ℕ):ℝ)
  have hΩ' : (Ω.card:ℝ) ≤ 4*(l:ℝ)^2 := by exact_mod_cast hΩ
  have hD' : (D.card:ℝ) ≤ (d:ℝ)^4 := by exact_mod_cast hD
  have hMain :
      ((joint hC Ω D).card:ℝ)*(L/((l*d:ℕ):ℝ))^4 =
      L^4*((Ω.card:ℝ)/(l:ℝ)^4)*density d D := by
    simp only [joint_card,Nat.cast_mul,density]
    field_simp [hll.ne',hdl.ne'] <;> ring
  have hLen' : 0 ≤ L := Nat.cast_nonneg _
  have hlbox : L ≤ 3*(B:ℝ) := by
    dsimp only [L]
    push_cast
    linarith only [hB']
  have hProd : (Ω.card:ℝ)*(D.card:ℝ) ≤ (4*(l:ℝ)^2)*(d:ℝ)^4 :=
    mul_le_mul hΩ' hD' (Nat.cast_nonneg _) (by positivity)
  have hDiv := div_le_div_of_nonneg_right hlbox hden.le
  have hCube := pow_le_pow_left₀ (div_nonneg hLen' hden.le) hDiv 3
  have hSmall := mask_error (l*d) B (Nat.mul_pos hl hd) hLen (joint hC Ω D)
  rw [hMain] at hSmall
  simp only [joint_card,Nat.cast_mul] at hSmall
  change |((accepted (l*d) B (joint hC Ω D)).card:ℝ)-
    L^4*((Ω.card:ℝ)/(l:ℝ)^4)*density d D| ≤ _
  calc
    _ ≤ ((Ω.card:ℝ)*(D.card:ℝ))*(15*(L/((l:ℝ)*(d:ℝ)))^3) := hSmall
    _ ≤ ((4*(l:ℝ)^2)*(d:ℝ)^4)*(15*((3*(B:ℝ))/((l:ℝ)*(d:ℝ)))^3) := by
      apply mul_le_mul hProd (mul_le_mul_of_nonneg_left hCube (by norm_num)) <;> positivity
    _ = _ := by field_simp [hll.ne',hdl.ne'] <;> ring

end ActualA4MediumCRTError318
