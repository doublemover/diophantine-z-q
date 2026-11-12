module
public import SelectedDenominatorPrimeFactor318
public section
noncomputable section
namespace SelectedExactEntryOrders318
open SelectedQuotientOrders318 ConcreteG8Domain GlobalGeneratorPoints318
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _
lemma multiple_zero_iff (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) :
    M • generator p rho hr=0 ↔ SelectedFormalEntry318.Entry p rho hr M := by
  constructor
  · intro hz
    exact entry_of_order_dvd p rho hr M (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  · intro he
    have hz := (QuotientAddGroup.eq_zero_iff (N := subgroup p rho hr) _).mpr he
    change (QuotientAddGroup.mk' (subgroup p rho hr))
      (ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom D
        ((M:ℤ) • R))=0 at hz
    rw [map_zsmul,map_zsmul,natCast_zsmul] at hz
    exact hz
lemma entry_iff (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) :
    SelectedFormalEntry318.Entry p rho hr M ↔ order p rho hr∣M :=
  (multiple_zero_iff p rho hr M).symm.trans addOrderOf_dvd_iff_nsmul_eq_zero.symm
end SelectedExactEntryOrders318
