module
public import Mathlib.NumberTheory.Height.NumberField
public section
noncomputable section
open NumberField Height IntermediateField
namespace RationalAbsoluteHeight
variable {K : Type*} [Field K] [NumberField K]

lemma iSup_pair (f : Fin 2 → ℝ) : (⨆ i, f i) = max (f 0) (f 1) := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finite.le_ciSup f 0) (Finite.le_ciSup f 1)

lemma finite_max_eq_one (q : ℚ) (v : FinitePlace K) :
    (⨆ i : Fin 2, v (![ (q.num : K), (q.den : K)] i)) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v n ≤ 1 := hv.apply_intCast_le_one (map_zero_le v 1) (map_one v)
    (map_neg_eq_map v)
  obtain ⟨a,b,hab⟩ := Rat.isCoprime_num_den q
  have hab' : (a:K)*(q.num:K)+(b:K)*(q.den:K)=1 := by exact_mod_cast hab
  have ha := hv ((a:K)*(q.num:K)) ((b:K)*(q.den:K))
  dsimp only at ha
  rw [hab', map_one, map_mul, map_mul] at ha
  have hb1 : v (a:K)*v (q.num:K) ≤ v (q.num:K) := by
    exact mul_le_of_le_one_left (apply_nonneg v _) (H a)
  have hb2 : v (b:K)*v (q.den:K) ≤ v (q.den:K) := by
    exact mul_le_of_le_one_left (apply_nonneg v _) (H b)
  rw [iSup_pair]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact le_antisymm (max_le (H q.num) (by simpa using H (q.den:ℤ)))
    (ha.trans (max_le_max hb1 hb2))

lemma mulHeight_ratCast (q : ℚ) :
    mulHeight₁ (q:K) = (max q.num.natAbs q.den : ℝ) ^ Module.finrank ℚ K := by
  have hden : (q.den:K) ≠ 0 := by exact_mod_cast q.den_nz
  have hn : (q.den:K)*(q:K)=(q.num:K) := by exact_mod_cast q.den_mul_eq_num
  have htuple : (q.den:K) • (![ (q:K), (1:K)] : Fin 2 → K) =
      ![(q.num:K),(q.den:K)] := by
    ext i
    fin_cases i <;> simp [hn]
  rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hden, htuple]
  rw [NumberField.mulHeight_eq (show (![ (q.num:K), (q.den:K)] : Fin 2 → K) ≠ 0 by
    intro hh; have h := congrFun hh 1; simpa using hden h)]
  simp_rw [finite_max_eq_one]
  rw [finprod_one, mul_one]
  have ha (v : InfinitePlace K) :
      (⨆ i : Fin 2, v (![ (q.num:K), (q.den:K)] i)) = (max q.num.natAbs q.den : ℝ) := by
    rw [iSup_pair]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      InfinitePlace.map_intCast, InfinitePlace.map_natCast]
    simp [Int.norm_eq_abs, Nat.cast_natAbs]
  simp_rw [ha]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

lemma absMulHeight_ratCast (F : Type*) [Field F] [CharZero F] (q : ℚ) :
    NumberField.absMulHeight₁ (q:F) = (max q.num.natAbs q.den : ℝ) := by
  have hx : IsIntegral ℚ (q:F) := by
    simpa using (isIntegral_algebraMap (R:=ℚ) (A:=F) (x:=q))
  let : FiniteDimensional ℚ ℚ⟮(q:F)⟯ := IntermediateField.adjoin.finiteDimensional hx
  let : NumberField ℚ⟮(q:F)⟯ := {}
  have hgen : IntermediateField.AdjoinSimple.gen ℚ (q:F) = (q:ℚ⟮(q:F)⟯) := by
    apply Subtype.ext
    simp [IntermediateField.AdjoinSimple.gen]
  rw [NumberField.absMulHeight₁, dite_eq_left hx]
  change (Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ (q:F))) ^
    (Module.finrank ℚ ℚ⟮(q:F)⟯ : ℝ)⁻¹ = _
  rw [hgen, mulHeight_ratCast]
  have hd : (Module.finrank ℚ ℚ⟮(q:F)⟯ : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=ℚ⟮(q:F)⟯)).ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hd, Real.rpow_one]

lemma absLogHeight_ratCast (F : Type*) [Field F] [CharZero F] (q : ℚ) :
    NumberField.absLogHeight₁ (q:F) = Real.log (max q.num.natAbs q.den : ℝ) := by
  rw [NumberField.absLogHeight₁, absMulHeight_ratCast]

lemma rational_box_of_absLogHeight_lt (F : Type*) [Field F] [CharZero F] (q : ℚ)
    (h : NumberField.absLogHeight₁ (q:F) < Real.log 9) :
    -9 ≤ q.num ∧ q.num ≤ 9 ∧ 1 ≤ q.den ∧ q.den ≤ 9 := by
  rw [absLogHeight_ratCast] at h
  have hden : 1 ≤ q.den := q.den_pos
  have hp : (0:ℝ) < (max q.num.natAbs q.den : ℝ) := by exact_mod_cast (lt_of_lt_of_le q.den_pos (le_max_right _ _))
  have hm : (max q.num.natAbs q.den : ℝ) < 9 := (Real.log_lt_log_iff hp (by norm_num)).mp h
  have hm' : max q.num.natAbs q.den ≤ 9 := by exact_mod_cast hm.le
  have hn := (le_max_left q.num.natAbs q.den).trans hm'
  have hd := (le_max_right q.num.natAbs q.den).trans hm'
  omega

#print axioms iSup_pair
#print axioms finite_max_eq_one
#print axioms mulHeight_ratCast
#print axioms absMulHeight_ratCast
#print axioms absLogHeight_ratCast
#print axioms rational_box_of_absLogHeight_lt
end RationalAbsoluteHeight
