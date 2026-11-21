module
public import OriginalCasselsOddTargetValuation318
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTOddDominantBinomialSquare318

open OriginalCasselsOddTargetValuation318 OriginalCasselsOddUnitSquare318

variable {p : ℕ} [Fact p.Prime]

/-- Actual completed-field odd Hensel lift for the additive binomial,
with its literal positive-valuation correction. -/
theorem one_add_square_of_positive (hp2 : p≠2) (u : ℚ_[p])
    (hu : 0<u.valuation) : ∃ s : ℚ_[p], s≠0 ∧ 1+u=s^2 := by
  have hu0 : u≠0 := by intro h; simpa [h] using hu
  obtain ⟨U,hU⟩ := actual_integral u hu.le
  have hSmall : ‖U‖<1 := by
    change ‖(U:ℚ_[p])‖<1
    rw [hU,Padic.norm_eq_zpow_neg_valuation hu0,← zpow_zero (p:ℝ)]
    apply (zpow_lt_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).mpr
    omega
  have hZ := (residue_zero_iff_norm U).mpr hSmall
  have hOne : PadicInt.toZMod (1+U)=1 := by rw [map_add,map_one,hZ,add_zero]
  obtain ⟨s,hs,hS⟩ := square_of_residue_one hp2 (1+U) hOne
  exact ⟨s,hs,by simpa only [PadicInt.coe_add,PadicInt.coe_one,hU] using hS⟩

end CTOddDominantBinomialSquare318
