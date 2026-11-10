module
public import SelectedPositiveDelta318
public section
noncomputable section
namespace SelectedQuotientOrders318
open ConcreteG8Domain (K D)
open GlobalGeneratorPoints318 (R)
open ReciprocalDouble318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def subgroup (rho : ℚ_[p]) (hr : rho^2=2) :
    AddSubgroup (E (ConcretePadic318.embedding p rho hr D)).Point :=
  AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue ℚ_[p])
    (ActualSplitOrbitEntry318.nonarchimedean p) _ (ActualSplitOrbitEntry318.coefficient_integral p rho hr)

/-- The actual half-point residue in the actual local formal quotient. -/
@[expose] def generator (rho : ℚ_[p]) (hr : rho^2=2) :
    (E (ConcretePadic318.embedding p rho hr D)).Point ⧸ subgroup p rho hr :=
  QuotientAddGroup.mk' (subgroup p rho hr)
    (ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom D R)

@[expose] def order (rho : ℚ_[p]) (hr : rho^2=2) : ℕ := addOrderOf (generator p rho hr)

lemma order_positive (rho : ℚ_[p]) (hr : rho^2=2) : 0<order p rho hr := by
  letI := CompactLocalPointCoding318.finite_formal_quotient
    (ActualSplitOrbitEntry318.nonarchimedean p)
    (ConcretePadic318.embedding p rho hr D)
    (ActualSplitOrbitEntry318.coefficient_ne p rho hr)
    (ActualSplitOrbitEntry318.coefficient_integral p rho hr)
  exact (isOfFinAddOrder_of_finite (generator p rho hr)).addOrderOf_pos

/-- Any proposed reduction-order modulus must kill this exact half-point
class. The comparison with Gaussian CM orders is kept explicit, not assumed
from membership of P=2R in a different doubling-image subgroup. -/
theorem entry_of_order_dvd (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ)
    (horder : order p rho hr∣M) : SelectedFormalEntry318.Entry p rho hr M := by
  have hz : M • generator p rho hr=0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp horder
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' (subgroup p rho hr))
    (ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom D
      ((M:ℤ) • R))=0
  rw [map_zsmul,map_zsmul,natCast_zsmul]
  exact hz

/-- Specializing the positive actual quotient order gives entry with no
existential local-modulus premise. Its arithmetic separation from OTHER
selected primes remains a separate requirement of the global prime theorem. -/
theorem actual_entry (rho : ℚ_[p]) (hr : rho^2=2) :
    0<order p rho hr ∧ SelectedFormalEntry318.Entry p rho hr (order p rho hr) :=
  ⟨order_positive p rho hr,entry_of_order_dvd p rho hr _ dvd_rfl⟩

end SelectedQuotientOrders318
