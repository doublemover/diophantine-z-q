module
public import CTOriginalGeometricRestrictionAction318
public import CTOriginalContinuousEllipticCocycles318
public import ActualTwoDescentActualGeometricCoboundary318
import all CTOriginalContinuousEllipticCocycles318
import all CTOriginalFullEllipticRepresentation318
import all ActualTwoDescentActualGeometricCoboundary318
public section
noncomputable section
namespace ActualTwoDescentFullCocycleRestriction318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open groupCohomology

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentGeometricRestrictionAction318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

open ActualTwoDescentFieldHalvingCocycle318
/-- Literal actual continuous restriction on full elliptic cocycles. -/
def fullCocycleRestriction (f : F →+* L) (n : F) (hn : n ≠ 0) :
    continuousFullCocycles n hn →+ continuousFullCocycles (f n) (field_map_ne_zero f hn) where
  toFun z := ⟨⟨fun σ => closurePointMap f n hn (z.val (Field.absoluteGaloisGroup.map f σ)),by
    apply (mem_cocycles₁_iff _).mpr
    intro σ τ
    change closurePointMap f n hn (z.val (Field.absoluteGaloisGroup.map f (σ*τ)))=_
    rw [map_mul,(mem_cocycles₁_iff _).mp z.val.property,map_add,actual_full_action,actual_closure_point_galois]⟩,(z.property.comp_continuous (Field.absoluteGaloisGroup.map f).continuous).comp (closurePointMap f n hn)⟩
  map_zero' := by apply Subtype.ext; apply Subtype.ext; funext σ; exact map_zero _
  map_add' z w := by apply Subtype.ext; apply Subtype.ext; funext σ; exact map_add _ _ _

lemma actual_full_restriction_boundary (f : F →+* L) (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) :
    fullCocycleRestriction f n hn (fullBoundary n hn Q)=
      fullBoundary (f n) (field_map_ne_zero f hn) (closurePointMap f n hn Q) := by
  apply Subtype.ext; apply Subtype.ext; funext σ
  change closurePointMap f n hn (halfDifference n hn Q (Field.absoluteGaloisGroup.map f σ))=_
  simp only [halfDifference,map_sub,actual_closure_point_galois]

end ActualTwoDescentFullCocycleRestriction318
