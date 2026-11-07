module
public import HCoefficients318
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public section
namespace HTail318
open HCoefficients318
variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def term (w : ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  (coefficient j : ℚ_[p]) * w^j

@[expose] noncomputable def H (w : ℚ_[p]) : ℚ_[p] := ∑' j, term p w j
@[expose] noncomputable def cubic (w : ℚ_[p]) : ℚ_[p] := ∑ j ∈ Finset.range 4, term p w j

/-- The p-adic argument is nonzero at a positive finite prescribed depth. -/
theorem argument_ne_zero (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) : w≠0 := by
  intro hz
  rw [hz,Padic.valuation_zero] at hw
  omega

theorem term_ne_zero (w : ℚ_[p]) (hw : w≠0) (j : ℕ) : term p w j ≠ 0 :=
  mul_ne_zero (Rat.cast_ne_zero.mpr (coefficient_ne_zero j)) (pow_ne_zero _ hw)

theorem term_valuation (w : ℚ_[p]) (hw : w≠0) (j : ℕ) :
    (term p w j).valuation=padicValRat p (coefficient j)+(j:ℤ)*w.valuation := by
  rw [term,Padic.valuation_mul (Rat.cast_ne_zero.mpr (coefficient_ne_zero j)) (pow_ne_zero _ hw),
    Padic.valuation_ratCast,Padic.valuation_pow]

theorem tail_term_valuation (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) (k : ℕ) :
    16*r+3*(k:ℤ) ≤ (term p w (k+4)).valuation := by
  rw [term_valuation p w (argument_ne_zero p w r hr hw),hw]
  have hc := tail_coefficient_valuation p hp k
  push_cast
  nlinarith [mul_nonneg (Int.natCast_nonneg k) (sub_nonneg.mpr hr)]

theorem tail_term_norm (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) (k : ℕ) :
    ‖term p w (k+4)‖ ≤ (p:ℝ)^(-(16*r+3*(k:ℤ))) := by
  rw [Padic.norm_eq_zpow_neg_valuation (term_ne_zero p w (argument_ne_zero p w r hr hw) (k+4))]
  apply zpow_le_zpow_right₀ (by exact_mod_cast (show 1≤p by omega))
  exact neg_le_neg (tail_term_valuation p hp w r hr hw k)

theorem geometric_factor (hp : 0<p) (r : ℤ) (k : ℕ) :
    (p:ℝ)^(-(16*r+3*(k:ℤ))) = (p:ℝ)^(-(16*r)) * ((p:ℝ)^(-3:ℤ))^k := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [←zpow_natCast,←zpow_mul,←zpow_add₀ hp0]
  congr 1
  ring

/-- A reusable full infinite-tail theorem, not a finite truncation calculation. -/
theorem summable_and_bound_of_decay (hp : 19≤p) (r : ℤ) (f : ℕ → ℚ_[p])
    (hf : ∀k,‖f k‖≤(p:ℝ)^(-(16*r+3*(k:ℤ)))) :
    Summable f ∧ ‖∑' k,f k‖≤(p:ℝ)^(-(16*r)) := by
  have hpos : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hone : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have hratio : ‖(p:ℝ)^(-3:ℤ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (zpow_pos hpos _)]
    exact (zpow_lt_one_iff_right₀ hone).mpr (by decide)
  have hg := (summable_geometric_of_norm_lt_one hratio).mul_left ((p:ℝ)^(-(16*r)))
  have hs : Summable f := hg.of_norm_bounded (fun k => by
    rw [←geometric_factor p (by omega) r k]
    exact hf k)
  refine ⟨hs,?_⟩
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  apply (hf k).trans
  apply zpow_le_zpow_right₀ hone.le
  omega

theorem tail_summable_and_bound (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    Summable (fun k => term p w (k+4)) ∧
      ‖∑' k,term p w (k+4)‖≤(p:ℝ)^(-(16*r)) :=
  summable_and_bound_of_decay p hp r _ (tail_term_norm p hp w r hr hw)

theorem series_summable (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) : Summable (term p w) :=
  (summable_nat_add_iff 4).mp (tail_summable_and_bound p hp w r hr hw).1

theorem series_hasSum (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) : HasSum (term p w) (H p w) :=
  (series_summable p hp w r hr hw).hasSum

theorem remainder_eq_tail (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    H p w - cubic p w = ∑' k,term p w (k+4) := by
  have hh := (series_summable p hp w r hr hw).sum_add_tsum_nat_add 4
  change cubic p w + (∑' k,term p w (k+4)) = H p w at hh
  rw [←hh]
  ring

theorem norm_le_iff_valuation (x : ℚ_[p]) (m : ℤ) :
    ‖x‖≤(p:ℝ)^(-m) ↔ (m : WithTop ℤ)≤Padic.addValuation x := by
  have hpos : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hone : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hx : x=0
  · subst x
    simpa only [norm_zero,Padic.addValuation.map_zero,le_top,iff_true] using
      (zpow_pos hpos (-m)).le
  · rw [Padic.norm_eq_zpow_neg_valuation hx,Padic.addValuation.apply hx]
    simp only [zpow_le_zpow_iff_right₀ hone,neg_le_neg_iff,WithTop.coe_le_coe]

/-- The entire actual H-series, after its cubic truncation, has valuation at
least 16r. No logarithm homomorphism or formal-group isometry is assumed. -/
theorem full_H_tail_precision (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    (16*r : WithTop ℤ)≤Padic.addValuation (H p w-cubic p w) := by
  apply (norm_le_iff_valuation p _ (16*r)).mp
  rw [remainder_eq_tail p hp w r hr hw]
  exact (tail_summable_and_bound p hp w r hr hw).2

end HTail318
#print axioms HTail318.series_hasSum
#print axioms HTail318.full_H_tail_precision
