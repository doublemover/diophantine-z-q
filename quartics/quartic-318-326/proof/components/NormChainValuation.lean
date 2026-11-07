module
public import QuarticOptimization
public section
namespace NormChainValuation

/-- The numerical backward step after the no-cancellation valuation identity.
R is the positive odd contact valuation; integrality, not oddness itself, is
what is used after those upper bounds have been supplied. -/
theorem backward_step (R m w previous leaf : ℤ)
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hw : 0 < 2*w+R)
    (hprevious : w ≤ 2*previous)
    (hleaf : w ≤ 2*leaf-(2*m-1)*R) :
    0 < 2*previous+R ∧ m ≤ leaf := by
  constructor
  · nlinarith
  · have hprod : 0 ≤ (4*m-3)*(R-1) :=
      mul_nonneg (by omega) (by omega)
    have hb : 4*m-3 < 4*leaf := by nlinarith
    omega

theorem negative_contact_impossible (R w : ℤ)
    (hw : w ≤ 0) (hpole : 0 < 2*w+R) : 0 < R := by omega

theorem real_step (previous weight leaf : ℚ)
    (hp : 1 ≤ previous) (hw : 0 ≤ weight) :
    1 ≤ previous^2+weight*leaf^2 := by
  have hh : 0 ≤ weight*leaf^2 := mul_nonneg hw (sq_nonneg leaf)
  nlinarith


theorem reciprocal_trace_bound (a b s : ℤ) (hs : min a b ≤ s) :
    a+b-s ≤ max a b := by omega

theorem reciprocal_trace_one_place (R a b s : ℤ) (hs : min a b ≤ s)
    (hpole : 0 < 2*(a+b-s)+R) : 0 < 2*a+R ∨ 0 < 2*b+R := by omega

end NormChainValuation
