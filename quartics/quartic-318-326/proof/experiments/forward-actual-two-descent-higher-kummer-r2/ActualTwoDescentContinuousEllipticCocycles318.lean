module
public import ActualTwoDescentFullEllipticRepresentation318
public section
noncomputable section
namespace ActualTwoDescentContinuousEllipticCocycles318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentFullEllipticRepresentation318

/-- Genuine locally constant cocycles with values in the ENTIRE geometric elliptic group. -/
def continuousFullCocycles (n : F) (hn : n ≠ 0) : AddSubgroup (cocycles₁ (fullEllipticRep n hn)) where
  carrier := {z | IsLocallyConstant (z : Gal → Point (algebraMap F Qbar n))}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun hx hy => (hx.prodMk hy).comp (fun z => z.1+z.2)
  neg_mem' := fun hx => hx.comp Neg.neg

def fullBoundary (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) : continuousFullCocycles n hn :=
  ⟨⟨halfDifference n hn Q,(mem_cocycles₁_iff _).mpr (actual_half_difference_cocycle n hn Q)⟩,
    (actual_galois_point_locally_constant n hn Q).comp (fun R => R-Q)⟩

lemma actual_full_boundary_add (n : F) (hn : n ≠ 0) (P Q : Point (algebraMap F Qbar n)) :
    fullBoundary n hn (P+Q)=fullBoundary n hn P+fullBoundary n hn Q := by
  apply Subtype.ext; apply Subtype.ext; funext σ
  change halfDifference n hn (P+Q) σ=halfDifference n hn P σ+halfDifference n hn Q σ
  simp only [halfDifference,map_add]
  abel

def fullClassHom (n : F) (hn : n ≠ 0) : continuousFullCocycles n hn →+ H1 (fullEllipticRep n hn) where
  toFun z := H1π (fullEllipticRep n hn) z
  map_zero' := map_zero _
  map_add' z w := map_add _ z.val w.val

lemma actual_full_boundary_zero (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) :
    fullClassHom n hn (fullBoundary n hn Q)=0 := by
  apply (H1π_eq_zero_iff _).mpr
  refine ⟨Q,?_⟩
  funext σ
  rfl

end ActualTwoDescentContinuousEllipticCocycles318
