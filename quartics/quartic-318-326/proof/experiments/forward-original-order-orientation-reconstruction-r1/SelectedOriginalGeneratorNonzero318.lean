module
public import SelectedExactEntryOrders318
public section
noncomputable section
namespace SelectedOriginalGeneratorNonzero318
open SelectedQuotientOrders318 SelectedEntryDenominatorDivisibility318
open SelectedIntegralPointNonformal318 SelectedGlobalCoordinateDenominators318
open GlobalGeneratorPoints318 ConcreteG8Domain WeierstrassCurve.Affine
lemma denominator_one : multipleDenominator 1=1 := by
  norm_num [multipleDenominator,pointDenominator,denominator,R,xR,pair,
    Point.xRep_some,Matrix.cons_val_zero]
variable (p : ℕ) [Fact p.Prime]
lemma generator_ne_zero (rho : ℚ_[p]) (hr : rho^2=2) : generator p rho hr≠0 := by
  intro hz
  have he := (SelectedExactEntryOrders318.multiple_zero_iff p rho hr 1).mp
    (by simpa only [one_nsmul] using hz)
  have hd := entry_divides p rho hr 1 (by decide) he
  rw [denominator_one] at hd
  exact (Fact.out : p.Prime).not_dvd_one hd
lemma order_gt_one (rho : ℚ_[p]) (hr : rho^2=2) : 1<order p rho hr := by
  have hp := order_positive p rho hr
  have hn : order p rho hr≠1 := by
    intro he
    exact generator_ne_zero p rho hr (AddMonoid.addOrderOf_eq_one_iff.mp he)
  omega
end SelectedOriginalGeneratorNonzero318
