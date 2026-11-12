module
public import ActualTwoDescentHigherFullLifting318
public section
noncomputable section
namespace ActualTwoDescentPowerRepresentationClass318
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
open ActualTwoDescentPowerCocycleRepresentation318 ActualTwoDescentPowerTorsionBoundaries318

def powerRepresentationCocycleHom (n : F) (hn : n ≠ 0) (k : ℕ) :
    powerValuedCocycles n hn k →+ cocycles₁ (powerTorsionRep n hn k) where
  toFun := powerRepresentationCocycle n hn k
  map_zero' := by apply Subtype.ext; funext σ; rfl
  map_add' z w := by apply Subtype.ext; funext σ; rfl

def powerMathlibClass (n : F) (hn : n ≠ 0) (k : ℕ) :
    powerValuedCocycles n hn k →+ H1 (powerTorsionRep n hn k) where
  toFun z := H1π (powerTorsionRep n hn k) (powerRepresentationCocycleHom n hn k z)
  map_zero' := by rw [map_zero,map_zero]
  map_add' z w := by rw [map_add,map_add]

lemma actual_power_mathlib_class_kernel (n : F) (hn : n ≠ 0) (k : ℕ) (z : powerValuedCocycles n hn k) :
    powerMathlibClass n hn k z=0 ↔ z ∈ (powerBoundaryHom n hn k).range := by
  change H1π _ (powerRepresentationCocycle n hn k z)=0 ↔ _
  rw [H1π_eq_zero_iff]
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    apply actual_power_cocycle_ext
    intro σ
    exact congrArg Subtype.val (congrFun hT σ)
  · rintro ⟨T,rfl⟩
    exact ⟨T,funext (fun σ => rfl)⟩

end ActualTwoDescentPowerRepresentationClass318
