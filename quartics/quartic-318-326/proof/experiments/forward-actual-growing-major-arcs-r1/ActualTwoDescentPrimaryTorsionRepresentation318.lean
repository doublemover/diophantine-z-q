module
public import ActualTwoDescentActualSelmerDirectLimit318
public section
noncomputable section
namespace ActualTwoDescentPrimaryTorsionRepresentation318
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

open ActualTwoDescentPrimaryGeometricCocycles318

def primaryTorsionAction (n : F) (hn : n ≠ 0) (σ : Gal) : geometricPrimary n →+ geometricPrimary n where
  toFun T := ⟨galoisPointHom σ n hn T.val,by
    obtain ⟨k,hk⟩ := T.property
    exact ⟨k,by rw [←map_nsmul,hk,map_zero]⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' T U := Subtype.ext (map_add _ T.val U.val)

def primaryTorsionRepresentation (n : F) (hn : n ≠ 0) : Representation ℤ Gal (geometricPrimary n) where
  toFun σ := (primaryTorsionAction n hn σ).toIntLinearMap
  map_one' := by ext P; exact Subtype.ext (actual_galois_one n hn P.val)
  map_mul' σ τ := by ext P; exact Subtype.ext (actual_galois_mul σ τ n hn P.val)

def primaryTorsionRep (n : F) (hn : n ≠ 0) : Rep ℤ Gal := Rep.of (primaryTorsionRepresentation n hn)

def primaryRepresentationCocycle (n : F) (hn : n ≠ 0) (z : primaryCocycles n hn) : cocycles₁ (primaryTorsionRep n hn) := by
  refine ⟨(fun σ => ⟨z.val.val σ,z.property σ⟩),?_⟩
  apply (mem_cocycles₁_iff _).mpr
  intro σ τ
  apply Subtype.ext
  exact (mem_cocycles₁_iff _).mp z.val.val.property σ τ

end ActualTwoDescentPrimaryTorsionRepresentation318
