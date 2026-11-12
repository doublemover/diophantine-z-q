module
public import ActualTwoDescentPrimaryTorsionRepresentation318
public section
noncomputable section
namespace ActualTwoDescentPrimaryRepresentationClass318
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
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318

open ActualTwoDescentPrimaryGeometricCocycles318 ActualTwoDescentPrimaryGeometricBoundary318
open ActualTwoDescentPrimaryTorsionRepresentation318

def primaryRepresentationCocycleHom (n : F) (hn : n ≠ 0) : primaryCocycles n hn →+ cocycles₁ (primaryTorsionRep n hn) where
  toFun := primaryRepresentationCocycle n hn
  map_zero' := by apply Subtype.ext; funext σ; rfl
  map_add' z w := by apply Subtype.ext; funext σ; rfl

def primaryMathlibClass (n : F) (hn : n ≠ 0) : primaryCocycles n hn →+ H1 (primaryTorsionRep n hn) where
  toFun z := H1π (primaryTorsionRep n hn) (primaryRepresentationCocycleHom n hn z)
  map_zero' := by rw [map_zero,map_zero]
  map_add' z w := by rw [map_add,map_add]

lemma actual_primary_mathlib_kernel (n : F) (hn : n ≠ 0) (z : primaryCocycles n hn) :
    primaryMathlibClass n hn z=0 ↔ z ∈ (primaryBoundaryHom n hn).range := by
  change H1π _ (primaryRepresentationCocycle n hn z)=0 ↔ _
  rw [H1π_eq_zero_iff]
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext σ
    exact congrArg Subtype.val (congrFun hT σ)
  · rintro ⟨T,rfl⟩
    exact ⟨T,funext (fun σ => rfl)⟩

end ActualTwoDescentPrimaryRepresentationClass318
