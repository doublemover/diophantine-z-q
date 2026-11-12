module
public import SelectedGlobalCoordinateDenominators318
public section
noncomputable section
namespace SelectedIntegralPointNonformal318
open ConcreteG8Domain ReciprocalDouble318 WeierstrassCurve.Affine
@[expose] def pointDenominator (Q : (E D).Point) : ℕ :=
  SelectedGlobalCoordinateDenominators318.denominator (Q.xRep 0)
lemma positive (Q : (E D).Point) : 0<pointDenominator Q :=
  SelectedGlobalCoordinateDenominators318.positive _
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _
/-- Nonzero global points with integral x-coordinate are not in the formal subgroup. -/
lemma not_formal (rho : ℚ_[p]) (hr : rho^2=2) (Q : (E D).Point)
    (hQ : Q≠0) (hd : ¬p∣pointDenominator Q) :
    ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom D Q ∉
      SelectedQuotientOrders318.subgroup p rho hr := by
  cases Q with
  | zero => exact (hQ rfl).elim
  | some x y hn =>
    have hx : ‖ConcretePadic318.embedding p rho hr x‖≤1 :=
      SelectedGlobalCoordinateDenominators318.embedded_integral p rho hr x hd
    rw [ShortCurveBaseChange318.pointMap_some]
    intro he
    change Point.some _ _ _=0 ∨ 1<‖ConcretePadic318.embedding p rho hr x‖ at he
    rcases he with hz|hpole
    · exact Point.some_ne_zero _ hz
    · exact (not_lt_of_ge hx) hpole
end SelectedIntegralPointNonformal318
