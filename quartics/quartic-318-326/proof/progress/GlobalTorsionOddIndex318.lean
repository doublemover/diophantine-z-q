module
public import GlobalGeneratorClosure318
public import GlobalDuplicationHeight318
public section
namespace GlobalTorsionOddIndex318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalNormClasses318
open GlobalSaturationHeight318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

lemma double_norm_square (Q:E.Point) : NormSquare (Q+Q) := by
  cases Q with
  | zero =>
    change NormSquare ((0:E.Point)+0)
    simp [NormSquare,Point.xRep,AnchorNorm318.norm_pair]
  | some x y h =>
    by_cases hy:y=0
    · subst y
      rw [Point.add_self_of_Y_eq (by simp [negY,E])]
      simp [NormSquare,Point.xRep,AnchorNorm318.norm_pair]
    · have hn:y≠E.negY x y := by
        simp only [negY,E,zero_mul,sub_zero]
        intro hh
        have hz:2*y=0 := by linear_combination hh
        exact (mul_ne_zero (by norm_num) hy) hz
      rw [Point.add_self_of_Y_ne hn]
      simp only [NormSquare,Point.xRep_some,Matrix.cons_val_zero]
      rw [ValuationDuplication318.actual_doubling_x x y h hy,AnchorNorm318.norm_pow]
      exact IsSquare.sq _

/-- The actual point R is not twice another point modulo any actual
2-torsion translate. This is the odd-index obstruction, independent of
finite generation and of any height theory. -/
theorem R_not_double_mod_torsion (Q U:E.Point) (hu:U+U=0) : R≠Q+Q+U := by
  intro he
  have hs:=double_norm_square Q
  have hh:R+U=Q+Q := by
    rw [he]
    calc
      Q+Q+U+U=(Q+Q)+(U+U) := by abel
      _ = Q+Q := by rw [hu,add_zero]
  rw [←hh] at hs
  rcases two_torsion_classification U hu with h0|⟨j,hj⟩
  · rw [h0,add_zero] at hs
    exact R_not_norm_square hs
  · rw [hj] at hs
    exact translate_not_norm_square j hs

lemma odd_index_of_representation (G U:E.Point) (m:ℤ) (hu:U+U=0)
    (hm:R=m • G+U) : Odd m := by
  by_contra hn
  have he:Even m := Int.not_odd_iff_even.mp hn
  obtain ⟨k,hk⟩:=he
  apply R_not_double_mod_torsion (k • G) U hu
  rw [hm,hk,add_zsmul]

lemma torsion_canonical_zero {H:E.Point→ℝ} (d:CanonicalData H)
    (Q:E.Point) (hq:IsOfFinAddOrder Q) : H Q=0 := by
  obtain ⟨n,hn,hzero⟩:=hq.exists_nsmul_eq_zero
  have hnZ:(n:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he:=d.zsmul (n:ℤ) Q
  rw [natCast_zsmul,hzero,d.zero] at he
  have hnR:(n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hnR)

lemma log392_lt_three_log9 : Real.log (392:ℝ)<3*Real.log 9 := by
  have hh:=Real.log_lt_log (by norm_num : (0:ℝ)<392) (by norm_num : (392:ℝ)<9^3)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

/-- The checked small-height certificate eliminates every possible
higher-order torsion point. No reduction-injection theorem is assumed. -/
theorem torsion_is_two_torsion {H:E.Point→ℝ} (d:CanonicalData H)
    (Q:E.Point) (hq:IsOfFinAddOrder Q) : Q+Q=0 := by
  have hz:=torsion_canonical_zero d Q hq
  have hlow:=d.lower Q
  rw [hz,mul_zero,zero_add] at hlow
  have hsmall:xHeight Q<Real.log 9 := by linarith [log392_lt_three_log9]
  have hc:=GlobalSaturation318.small_height_classified PrimitiveQuadraticMahler318.polynomial_height_coverage Q hsmall
  rcases hc with ht|⟨U,hu,he⟩
  · exact ht
  · have hheight:=classified_height d Q (Or.inr ⟨U,hu,he⟩)
    have hp:=GlobalHeightPositivity318.canonical_R_positive d
    have heq:H Q=H R := by
      rcases he with hplus|hminus
      · rw [hplus,d.torsion _ _ hu]
      · rw [hminus,canonical_neg d,d.torsion _ _ hu]
    linarith

#print axioms R_not_double_mod_torsion
#print axioms odd_index_of_representation
#print axioms torsion_is_two_torsion
end
end GlobalTorsionOddIndex318
