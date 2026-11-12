module
public import ActualTwoDescentOriginalStalkFactorsRebuild318
public section
noncomputable section
namespace ActualTwoDescentDVRValueTransportRebuild318
open IsDiscreteValuationRing
variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
/-- This is the integral part of the surviving geometry producer
ActualDvrFractionValuationTransport318.integral_value, reused explicitly.
It proves normalization, not just equivalence of valuation supports. -/
lemma value (e : R ≃+* S) (x : R) : addVal S (e x) = addVal R x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, addVal_zero, addVal_zero]
  · obtain ⟨π, hπ⟩ := exists_prime R
    obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ.irreducible
    have hi : Irreducible (e π) :=
      (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr hπ.irreducible
    have he : e x = (Units.map e.toMonoidHom u : Sˣ) * (e π)^n := by
      rw [hu, map_mul, map_pow] <;> rfl
    rw [addVal_def x u hπ.irreducible n hu,
      addVal_def (e x) (Units.map e.toMonoidHom u) hi n he]
end ActualTwoDescentDVRValueTransportRebuild318
