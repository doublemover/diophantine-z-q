module
public import ActualTwoDescentFullEllipticHOneKernel318
public section
noncomputable section
namespace ActualTwoDescentTorsionIntoFullCocycles318
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

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318

/-- Literal inclusion E[2]→E on every cocycle value, retaining actual local constancy. -/
def torsionFullCocycle (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) : continuousFullCocycles n hn :=
  ⟨⟨fun σ => (((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd : Point (algebraMap F Qbar n)),by
    apply (mem_cocycles₁_iff _).mpr
    intro σ τ
    rw [actual_full_action,actual_two_torsion_fixed_subtype]
    have h := congrArg (fun T : Multiplicative (closedTwoTorsion n) => (T.toAdd : Point (algebraMap F Qbar n)))
      ((χ : Gal →* Multiplicative (closedTwoTorsion n)).map_mul σ τ)
    exact h.trans (add_comm _ _)⟩,
    χ.property.comp (fun T : Multiplicative (closedTwoTorsion n) => (T.toAdd : Point (algebraMap F Qbar n)))⟩

lemma actual_torsion_full_mul (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    torsionFullCocycle n hn (χ*ψ)=torsionFullCocycle n hn χ+torsionFullCocycle n hn ψ := by
  apply Subtype.ext; apply Subtype.ext; funext σ; rfl

def torsionFullClass (n : F) (hn : n ≠ 0) : continuousCocycles n →* Multiplicative (H1 (fullEllipticRep n hn)) where
  toFun χ := Multiplicative.ofAdd (fullClassHom n hn (torsionFullCocycle n hn χ))
  map_one' := by
    have h : torsionFullCocycle n hn 1=0 := by apply Subtype.ext; apply Subtype.ext; funext σ; rfl
    change Multiplicative.ofAdd (fullClassHom n hn (torsionFullCocycle n hn 1))=1
    rw [h,map_zero]; rfl
  map_mul' χ ψ := by
    change Multiplicative.ofAdd (fullClassHom n hn (torsionFullCocycle n hn (χ*ψ)))=_
    rw [actual_torsion_full_mul,map_add]
    rfl

lemma actual_torsion_full_double (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    torsionFullCocycle n hn χ+torsionFullCocycle n hn χ=0 := by
  apply Subtype.ext; apply Subtype.ext; funext σ
  exact (show _+_=0 from by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using
      (((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd).property)

lemma actual_torsion_full_class_two (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    (torsionFullClass n hn χ)^2=1 := by
  change Multiplicative.ofAdd (fullClassHom n hn (torsionFullCocycle n hn χ))^2=1
  rw [pow_two]
  change fullClassHom n hn (torsionFullCocycle n hn χ)+fullClassHom n hn (torsionFullCocycle n hn χ)=0
  rw [←map_add,actual_torsion_full_double,map_zero]

end ActualTwoDescentTorsionIntoFullCocycles318
