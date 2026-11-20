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

open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentFieldGaloisPointAction318
/-- Literal actual continuous restriction on full elliptic cocycles. -/
def fullCocycleRestriction (f : F →+* L) (n : F) (hn : n ≠ 0) :
    continuousFullCocycles n hn →+ continuousFullCocycles (f n) (field_map_ne_zero f hn) where
  toFun z := ⟨⟨fun σ => closurePointMap f n hn (z.val (Field.absoluteGaloisGroup.map f σ)),by
    apply (mem_cocycles₁_iff _).mpr
    intro σ τ
    let φ := Field.absoluteGaloisGroup.map f
    let c : Gal → Point (algebraMap F Qbar n) := z.val.val
    let b := closurePointMap f n hn
    let hn' := field_map_ne_zero f hn
    let a := galoisPointHom (φ σ) n hn (c (φ τ))
    let aSource : Point (algebraMap F Qbar n) :=
      (fullEllipticRep n hn).ρ (φ σ) (c (φ τ))
    let aTarget : Point (algebraMap L (AlgebraicClosure L) (f n)) :=
      (fullEllipticRep (f n) hn').ρ σ (b (c (φ τ)))
    have hc := (mem_cocycles₁_iff (A := fullEllipticRep n hn) z.val.val).1
      z.val.property (φ σ) (φ τ)
    change c (φ σ * φ τ) = aSource + c (φ σ) at hc
    have hSource : aSource = a := actual_full_action n hn (φ σ) (c (φ τ))
    have hTarget : aTarget = galoisPointHom σ (f n) hn' (b (c (φ τ))) :=
      actual_full_action (f n) hn' σ (b (c (φ τ)))
    have hs : c (φ σ * φ τ) = a + c (φ σ) :=
      hc.trans (congrArg (fun P : Point (algebraMap F Qbar n) => P + c (φ σ)) hSource)
    change b (c (φ (σ*τ))) = aTarget + b (c (φ σ))
    calc
      b (c (φ (σ*τ))) = b (c (φ σ * φ τ)) :=
        congrArg (fun g : Gal => b (c g)) (map_mul φ σ τ)
      _ = b (a + c (φ σ)) := congrArg (fun P : Point (algebraMap F Qbar n) => b P) hs
      _ = b a + b (c (φ σ)) := b.map_add _ _
      _ = galoisPointHom σ (f n) hn' (b (c (φ τ))) + b (c (φ σ)) :=
        congrArg (fun P : Point (algebraMap L (AlgebraicClosure L) (f n)) => P + b (c (φ σ)))
          (actual_closure_point_galois f n hn σ (c (φ τ)))
      _ = aTarget + b (c (φ σ)) :=
        congrArg (fun P : Point (algebraMap L (AlgebraicClosure L) (f n)) => P + b (c (φ σ)))
          hTarget.symm⟩,
    (z.property.comp_continuous (Field.absoluteGaloisGroup.map f).continuous).comp (closurePointMap f n hn)⟩
  map_zero' := by apply Subtype.ext; apply Subtype.ext; funext σ; exact map_zero _
  map_add' z w := by apply Subtype.ext; apply Subtype.ext; funext σ; exact map_add _ _ _

lemma actual_full_restriction_boundary (f : F →+* L) (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) :
    fullCocycleRestriction f n hn (fullBoundary n hn Q)=
      fullBoundary (f n) (field_map_ne_zero f hn) (closurePointMap f n hn Q) := by
  apply Subtype.ext; apply Subtype.ext; funext σ
  let b := closurePointMap f n hn
  let hn' := field_map_ne_zero f hn
  let φ := Field.absoluteGaloisGroup.map f
  change b (halfDifference n hn Q (φ σ)) = halfDifference (f n) hn' (b Q) σ
  change b (galoisPointHom (φ σ) n hn Q - Q) =
    galoisPointHom σ (f n) hn' (b Q) - b Q
  exact (b.map_sub _ Q).trans
    (congrArg (fun P : Point (algebraMap L (AlgebraicClosure L) (f n)) => P - b Q)
      (actual_closure_point_galois f n hn σ Q))

end ActualTwoDescentFullCocycleRestriction318
