module
public import SheafCohomologyRetraction318
public import OpenMayerVietoris318
public import LocalSheafCohomologyAdditive318
public import LocalAffineStructureHOne318
public section
noncomputable section
namespace AffineCoverHOnePresentation318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} [IsIntegral X]

/-- A genuine additive connecting map from original sections on the overlap to original global H1. -/
@[expose] def boundary (U V : X.Opens) (h : U ⊔ V = ⊤) :
    Γ(X,U ⊓ V) →+ SheafCohomologyRetraction318.structureH X 1 :=
  (OpenMayerVietoris318.boundary (StructureAdditiveSheaf318.sheaf X) U V h).comp
    (LocalSheafCohomologyAdditive318.zeroAddEquiv
      (StructureAdditiveSheaf318.sheaf X) (U ⊓ V)).symm.toAddMonoidHom

/-- Every actual global H1 class comes from an actual regular function on the overlap. -/
theorem boundary_surjective (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) : Function.Surjective (boundary U V h) :=
  (OpenMayerVietoris318.boundary_surjective (StructureAdditiveSheaf318.sheaf X) U V h
    (LocalAffineStructureHOne318.eq_zero U hU) (LocalAffineStructureHOne318.eq_zero V hV)).comp
      (LocalSheafCohomologyAdditive318.zeroAddEquiv
        (StructureAdditiveSheaf318.sheaf X) (U ⊓ V)).symm.surjective
end AffineCoverHOnePresentation318
