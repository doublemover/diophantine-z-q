module
public import OriginalActualSexticInt318

/-! Actual reconstructed sparse arithmetic jet at T=119136.
The only field inputs are the three exact defining radical relations of
the representative. Their geometric marked orientation, physical central
twist, and comparison with the original polarized family are separate. -/
public section
noncomputable section

namespace OriginalActualSparseJetArithmetic318

open Polynomial OriginalSexticIntegralTower318 OriginalSexticCoefficientAudit318
open OriginalActualSexticInt318

variable {E : Type*} [Field E]

structure Lift (E : Type*) [Field E] where
  alpha : E
  beta : E
  rho : E
  alpha_relation : alpha^2 = (alphaSq : E)
  beta_relation : beta^2 = (betaSq : E)
  rho_relation : rho^2 = read4 alpha beta rhoSq

@[expose] def Lift.read (L : Lift E) : V8 →+ E := read8 L.alpha L.beta L.rho

theorem Lift.mul (L : Lift E) (a b : V8) :
    L.read (m8 alphaSq betaSq rhoSq a b) = L.read a * L.read b :=
  read8_mul _ _ _ _ _ _ L.alpha_relation L.beta_relation L.rho_relation a b

@[simp] theorem Lift.one (L : Lift E) : L.read unit = 1 := read8_unit _ _ _

local notation "cd" => C (denom : E)
local notation "ci" => C ((denom : E)⁻¹)

private theorem denom_ne [CharZero E] : (denom : E) ≠ 0 :=
  Int.cast_ne_zero.mpr (ne_of_gt denom_pos)

private theorem cancel_ci [CharZero E] : ci * cd = (1 : E[X]) := by
  rw [← map_mul, inv_mul_cancel₀ denom_ne, map_one]

@[expose] def Lift.unscale (L : Lift E) {n : ℕ} (t : Table n) : E[X] :=
  ci * readPoly L.read t

private theorem rawF_derivative_degree (L : Lift E) :
    (readPoly L.read f).derivative.natDegree ≤ 5 :=
  (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (readPoly_degree _ _) _)

theorem true_F_degree [CharZero E] (L : Lift E) : (L.unscale f).natDegree = 6 := by
  have h : (L.unscale f).natDegree ≤ 6 := (natDegree_C_mul_le _ _).trans (readPoly_degree _ _)
  refine natDegree_eq_of_le_of_coeff_ne_zero h ?_
  change (ci * readPoly L.read f).coeff 6 ≠ 0
  rw [coeff_C_mul, readPoly_coeff, OriginalSexticCoefficientAudit318.coeff, dite_eq_left (by decide : 6 < 6+1)]
  have hraw : L.read (f 6) = (denom : E) := by
    rw [monic_table, read_zsmul, Lift.one, mul_one]
  rw [show (⟨6, by decide⟩ : Fin 7) = 6 by rfl, hraw, inv_mul_cancel₀ denom_ne]
  exact one_ne_zero

theorem true_F_monic [CharZero E] (L : Lift E) : (L.unscale f).leadingCoeff = 1 := by
  rw [leadingCoeff, true_F_degree, Lift.unscale, coeff_C_mul, readPoly_coeff, OriginalSexticCoefficientAudit318.coeff,
    dite_eq_left (by decide : 6 < 6+1)]
  change (denom:E)⁻¹ * L.read (f 6) = 1
  rw [monic_table, read_zsmul, Lift.one, mul_one, inv_mul_cancel₀ denom_ne]

private theorem scaled_relation (L : Lift E) (k : Fin 3) :
    cd * (X ^ (k : ℕ) * readPoly L.read g) -
      readPoly L.read (rs k) * (readPoly L.read f).derivative =
      readPoly L.read f * readPoly L.read (qs k) := by
  apply eq_of_upto _ _ 11
  · apply natDegree_sub_le_of_le (m := 11) (n := 11)
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_mul_le_of_le (natDegree_X_pow_le (k:ℕ)) (readPoly_degree _ _)).trans (by omega))
    · exact (natDegree_mul_le_of_le (readPoly_degree _ _) (rawF_derivative_degree L)).trans (by decide)
  · exact (natDegree_mul_le_of_le (readPoly_degree _ _) (readPoly_degree _ _)).trans (by decide)
  · intro i
    rw [coeff_sub, coeff_C_mul, read_shift _ _ _ (readPoly_coeff L.read g),
      read_convolve _ _ _ _ L.mul _ _ _ _ (readPoly_coeff L.read (rs k)) (readPoly_diff L.read f),
      read_convolve _ _ _ _ L.mul _ _ _ _ (readPoly_coeff L.read f) (readPoly_coeff L.read (qs k)),
      ← read_zsmul, ← map_sub]
    exact congrArg L.read (eq_kernel k i)

private theorem scaled_inverse (L : Lift E) :
    readPoly L.read inv * (readPoly L.read f).derivative -
      cd^2 = readPoly L.read f * readPoly L.read invQ := by
  apply eq_of_upto _ _ 11
  · apply natDegree_sub_le_of_le (m := 11) (n := 11)
    · exact (natDegree_mul_le_of_le (readPoly_degree _ _) (rawF_derivative_degree L)).trans (by decide)
    · rw [← map_pow, natDegree_C]
      decide
  · exact (natDegree_mul_le_of_le (readPoly_degree _ _) (readPoly_degree _ _)).trans (by decide)
  · intro i
    have hc : (cd^2).coeff i = L.read (constantCoeff ((denom * denom) • unit) i) := by
      rw [← map_pow, ← read_constant]
      simp only [read_zsmul, Lift.one, Int.cast_mul, mul_one, pow_two]
    rw [coeff_sub, hc,
      read_convolve _ _ _ _ L.mul _ _ _ _ (readPoly_coeff L.read inv) (readPoly_diff L.read f),
      read_convolve _ _ _ _ L.mul _ _ _ _ (readPoly_coeff L.read f) (readPoly_coeff L.read invQ),
      ← map_sub]
    exact congrArg L.read (inv_kernel i)

theorem true_relation [CharZero E] (L : Lift E) (k : Fin 3) :
    X^(k:ℕ) * L.unscale g - L.unscale (rs k) * (L.unscale f).derivative =
      L.unscale f * L.unscale (qs k) := by
  simp only [Lift.unscale, derivative_C_mul]
  calc
    _ = ci^2 * (cd * (X ^ (k : ℕ) * readPoly L.read g) -
       readPoly L.read (rs k) * (readPoly L.read f).derivative) := by
      linear_combination -(ci * X^(k:ℕ) * readPoly L.read g) * (cancel_ci (E := E))
    _ = _ := by rw [scaled_relation]; ring

theorem true_inverse [CharZero E] (L : Lift E) :
    L.unscale inv * (L.unscale f).derivative - 1 = L.unscale f * L.unscale invQ := by
  simp only [Lift.unscale, derivative_C_mul]
  calc
    _ = ci^2 * (readPoly L.read inv * (readPoly L.read f).derivative - cd^2) := by
      linear_combination (ci * cd + 1) * (cancel_ci (E := E))
    _ = _ := by rw [scaled_inverse]; ring

@[expose] def data [CharZero E] (L : Lift E) : OriginalSeparableSexticJet318.Data E where
  F := L.unscale f
  G := L.unscale g
  degree := true_F_degree L
  jet_degree := (natDegree_C_mul_le _ _).trans ((readPoly_degree _ _).trans (by decide))
  inverse := L.unscale inv
  inverse_quotient := L.unscale invQ
  inverse_relation := true_inverse L
  remainder := fun k => L.unscale (rs k)
  small := fun _ => (natDegree_C_mul_le _ _).trans (readPoly_degree _ _)
  relation := fun k => ⟨L.unscale (qs k), true_relation L k⟩

theorem squarefree [CharZero E] (L : Lift E) : (data L).F.Separable :=
  OriginalSeparableSexticJet318.separable (data L)

@[expose] def literalRawB (L : Lift E) : E := ((denom:E)⁻¹)^2 * L.read exactB

/-- Same reconstructed arithmetic wedge. No original PEL comparison is
deduced from this field calculation. -/
theorem evaluatedRawB [CharZero E] (L : Lift E) :
    OriginalSexticJetMarked318.rawB
      (OriginalSeparableSexticJet318.splittingCertificate (data L)) = literalRawB L := by
  let m (k : Fin 3) : E := -2 * ((L.unscale (rs k)).coeff 5 / (L.unscale f).leadingCoeff)
  change m 0 * m 2 - m 1^2 = literalRawB L
  have h (k : Fin 3) : m k = (denom:E)⁻¹ * (-2 * L.read (rs k 5)) := by
    rw [show m k = -2 * ((L.unscale (rs k)).coeff 5 / (L.unscale f).leadingCoeff) by rfl,
      true_F_monic, div_one, Lift.unscale, coeff_C_mul, readPoly_coeff, OriginalSexticCoefficientAudit318.coeff,
      dite_eq_left (by decide : 5 < 5+1)]
    change -2 * ((denom:E)⁻¹ * L.read (rs k 5)) = _
    ring
  rw [h, h, h, literalRawB, show rs 0 = r0 by rfl, show rs 1 = r1 by rfl, show rs 2 = r2 by rfl]
  have e := congrArg L.read det_kernel
  simp only [map_sub, L.mul, read_zsmul, Int.cast_neg, Int.cast_ofNat] at e
  linear_combination ((denom:E)⁻¹)^2 * e

end OriginalActualSparseJetArithmetic318

#print axioms OriginalActualSparseJetArithmetic318.squarefree
#print axioms OriginalActualSparseJetArithmetic318.true_relation

#print axioms OriginalActualSparseJetArithmetic318.evaluatedRawB
