module
public import OriginalCasselsOddUnitSquare318
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace OriginalCasselsOddTargetValuation318

open OriginalCasselsOddUnitSquare318 ActualTwoDescentLocalValuationTools318

variable {p : ℕ} [Fact p.Prime]

theorem actual_integral (x : ℚ_[p]) (hx : 0≤x.valuation) :
    ∃ X : ℤ_[p], (X:ℚ_[p])=x :=
  ⟨⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hx⟩,rfl⟩

theorem square_of_residue_one (hp2 : p≠2) (A : ℤ_[p]) (hA : PadicInt.toZMod A=1) :
    ∃ r : ℚ_[p], r≠0 ∧ (A:ℚ_[p])=r^2 := by
  obtain ⟨r,hr,h⟩ := unit_ratio_square_of_equal_residue hp2 A 1
    (by rw [map_one]; exact one_ne_zero) (by rwa [map_one])
  exact ⟨r,hr,by simpa only [PadicInt.coe_one,one_mul] using h⟩

private theorem norm_lt_one_of_positive_val {x : ℚ_[p]} (hx : x≠0)
    (hv : 0<x.valuation) : ‖x‖<1 := by
  rw [Padic.norm_eq_zpow_neg_valuation hx,←zpow_zero (p:ℝ)]
  apply (zpow_lt_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).2
  omega

theorem dominant_unit_square (hp2 : p≠2) (x : ℚ_[p]) (hx : x≠0) (hv : 0<x.valuation) :
    ∃ r : ℚ_[p], r≠0 ∧ 1-x+x^2=r^2 := by
  obtain ⟨X,hX⟩ := actual_integral x hv.le
  have hred : PadicInt.toZMod X=0 := by
    apply (residue_zero_iff_norm X).mpr
    rw [PadicInt.norm_def,hX]
    exact norm_lt_one_of_positive_val hx hv
  obtain ⟨r,hr,he⟩ := square_of_residue_one hp2 (1-X+X^2) (by
    simp only [map_add,map_sub,map_one,map_pow,hred,sub_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero])
  refine ⟨r,hr,?_⟩
  simpa only [PadicInt.coe_add,PadicInt.coe_sub,PadicInt.coe_one,PadicInt.coe_pow,hX] using he

/-- The same literal polynomial factor is a nonzero square whenever its
two comparing abscissae have unequal signed p-adic valuations. That
isolates the finite normalized boundary |x|=|4n| at every odd prime. -/
theorem factor_square_of_unequal_val (hp2 : p≠2) (n x : ℚ_[p]) (hn : n≠0) (hx : x≠0)
    (hval : x.valuation≠((4:ℚ_[p])*n).valuation) :
    ∃ s : ℚ_[p], s≠0 ∧ x^2-4*n*x+16*n^2=s^2 := by
  let u := (4:ℚ_[p])*n
  have hu : u≠0 := mul_ne_zero (by norm_num) hn
  have hdisj : x.valuation<u.valuation ∨ u.valuation<x.valuation := lt_or_gt_of_ne hval
  rcases hdisj with h|h
  · have hv : 0<(u/x).valuation := by
      rw [actual_valuation_div _ _ hu hx]
      exact sub_pos.mpr h
    obtain ⟨r,hr,hR⟩ := dominant_unit_square hp2 (u/x) (div_ne_zero hu hx) hv
    refine ⟨x*r,mul_ne_zero hx hr,?_⟩
    calc
      _=x^2*(1-u/x+(u/x)^2) := by dsimp [u]; field_simp [hx] <;> ring
      _=_ := by rw [hR]; ring
  · have hv : 0<(x/u).valuation := by
      rw [actual_valuation_div _ _ hx hu]
      exact sub_pos.mpr h
    obtain ⟨r,hr,hR⟩ := dominant_unit_square hp2 (x/u) (div_ne_zero hx hu) hv
    refine ⟨u*r,mul_ne_zero hu hr,?_⟩
    calc
      _=u^2*(1-x/u+(x/u)^2) := by
        have he : x^2-4*n*x+16*n^2=x^2-u*x+u^2 := by dsimp [u]; ring
        rw [he]
        field_simp [hu] <;> ring
      _=_ := by rw [hR]; ring

theorem abscissa_square_of_factor_square (n x y : ℚ_[p]) (hx : x≠0)
    (he : y^2=x*(x^2-4*n*x+16*n^2))
    (hfactor : ∃ s : ℚ_[p], s≠0 ∧ x^2-4*n*x+16*n^2=s^2) :
    ∃ r : ℚ_[p], r≠0 ∧ x=r^2 := by
  obtain ⟨s,hs,hS⟩ := hfactor
  rw [hS] at he
  have hy : y≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at he
    exact mul_ne_zero hx (pow_ne_zero _ hs) he.symm
  refine ⟨y/s,div_ne_zero hy hs,?_⟩
  rw [div_pow,he]
  field_simp [hs] <;> ring

end OriginalCasselsOddTargetValuation318

#print axioms OriginalCasselsOddTargetValuation318.factor_square_of_unequal_val
