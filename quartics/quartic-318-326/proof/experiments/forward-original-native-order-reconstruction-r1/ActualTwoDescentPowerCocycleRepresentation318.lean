module
public import ActualTwoDescentPowerValuedCocycles318
public section
noncomputable section
namespace ActualTwoDescentPowerCocycleRepresentation318
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

open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentPowerValuedCocycles318

/-- Literal comparison with Mathlib cocycles for the ACTUAL nontrivial E[2^k] representation. -/
def powerRepresentationCocycle (n : F) (hn : n ≠ 0) (k : ℕ) (z : powerValuedCocycles n hn k) :
    cocycles₁ (powerTorsionRep n hn k) := by
  refine ⟨(fun σ => ⟨z.val.val σ,z.property σ⟩),?_⟩
  apply (mem_cocycles₁_iff _).mpr
  intro σ τ
  apply Subtype.ext
  exact (mem_cocycles₁_iff _).mp z.val.val.property σ τ

lemma actual_power_representation_locally_constant (n : F) (hn : n ≠ 0) (k : ℕ)
    (z : powerValuedCocycles n hn k) : IsLocallyConstant (powerRepresentationCocycle n hn k z : Gal → geometricPowerTorsion n k) := by
  apply IsLocallyConstant.desc _ (fun T : geometricPowerTorsion n k => T.val)
  · exact z.val.property
  · exact Subtype.val_injective

end ActualTwoDescentPowerCocycleRepresentation318
