module
public import ActualTwoDescentHigherFreeFiniteIndex318
public section
noncomputable section
namespace ActualTwoDescentHigherRationalQuotientFinite318
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

open ActualTwoDescentHigherMultiplesTransport318 ActualTwoDescentHigherFreeFiniteIndex318
open ActualTwoDescentActualMordellWeilStructure318 ActualTwoDescentEllipticDoubleQuotient318

/-- All actual higher rational quotients are finite, produced from the genuine Mordell-Weil decomposition. -/
lemma actual_higher_rational_quotient_finite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (k : ℕ) : Finite (Point n ⧸ multiples (Point n) (2^k)) := by
  obtain ⟨r,T,hT,hfin,⟨e⟩,_⟩ := actual_mordell_weil_structure n hn hf
  letI := hT
  letI := hfin
  apply Nat.finite_of_card_ne_zero
  rw [actual_higher_free_finite_index r T e]
  exact (mul_pos (pow_pos (pow_pos (by decide) k) r) Nat.card_pos).ne'

end ActualTwoDescentHigherRationalQuotientFinite318
