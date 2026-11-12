module
public import ActualTwoDescentBoundedNaturalStabilization318
public section
noncomputable section
namespace ActualTwoDescentFiniteTorsionStabilization318
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

open ActualTwoDescentHigherMultiplesTransport318 ActualTwoDescentFiniteTorsionLevelGrowth318
open ActualTwoDescentBoundedNaturalStabilization318

/-- The actual finite Mordell-Weil factor has eventually constant2-power torsion, with a positive actual cardinal constant. -/
theorem actual_finite_torsion_stabilizes (T : Type*) [AddCommGroup T] [Finite T] :
    ∃ N C : ℕ, 0<C ∧ ∀ k, N ≤ k → Nat.card (torsionKernel T (2^k))=C := by
  obtain ⟨N,hN⟩ := actual_bounded_monotone_stabilizes (fun k => Nat.card (torsionKernel T (2^k)))
    (actual_torsion_kernel_card_monotone T) (Nat.card T) (actual_torsion_kernel_card_bound T)
  exact ⟨N,Nat.card (torsionKernel T (2^N)),Nat.card_pos,hN⟩

end ActualTwoDescentFiniteTorsionStabilization318
