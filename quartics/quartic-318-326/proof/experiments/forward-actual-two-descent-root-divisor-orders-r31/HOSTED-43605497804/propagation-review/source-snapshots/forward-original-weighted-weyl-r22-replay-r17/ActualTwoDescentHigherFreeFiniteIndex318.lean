module
public import ActualTwoDescentHigherMultiplesTransport318
public section
noncomputable section
namespace ActualTwoDescentHigherFreeFiniteIndex318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

open ActualTwoDescentHigherMultiplesTransport318

lemma actual_free_multiples_index (r m : ℕ) : (multiples (Fin r →₀ ℤ) m).index=m^r := by
  simpa only [Module.finrank_finsupp_self,Fintype.card_fin] using AddSubgroup.index_range_nsmul (Fin r →₀ ℤ) m

lemma actual_finite_multiples_index (T : Type*) [AddCommGroup T] [Finite T] (m : ℕ) :
    (multiples T m).index=Nat.card (torsionKernel T m) := by
  letI : (torsionKernel T m).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact AddSubgroup.index_range

/-- Actual higher rational quotient formula for an actual free/finite decomposition. -/
theorem actual_higher_free_finite_index {A : Type*} [AddCommGroup A] (r : ℕ)
    (T : Type*) [AddCommGroup T] [Finite T] (e : A ≃+ (Fin r →₀ ℤ) × T) (m : ℕ) :
    Nat.card (A ⧸ multiples A m)=m^r*Nat.card (torsionKernel T m) := by
  rw [←AddSubgroup.index_eq_card,actual_multiples_index_equiv e m,actual_multiples_prod,
    AddSubgroup.index_prod,actual_free_multiples_index,actual_finite_multiples_index]

end ActualTwoDescentHigherFreeFiniteIndex318
