module
public import ActualTwoDescentTorsionIntoFullCocycles318
public section
noncomputable section
namespace ActualTwoDescentFullConnectingExactness318
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
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentTorsionIntoFullCocycles318

/-- Exact Kummer sequence at H1(E[2]): its kernel in ACTUAL full elliptic H1 is the ACTUAL rational connecting image. -/
theorem actual_full_connecting_exact (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    torsionFullClass n hn χ=1 ↔ χ ∈ rationalCocycleImage n hn := by
  change fullClassHom n hn (torsionFullCocycle n hn χ)=0 ↔ _
  rw [actual_full_class_zero]
  constructor
  · rintro ⟨Q,hQ⟩
    have hfixed (σ : Gal) : galoisPointHom σ n hn (Q+Q)=Q+Q := by
      have ht := congrArg (fun z : continuousFullCocycles n hn => (z.val : Gal → Point (algebraMap F Qbar n)) σ)
        (actual_torsion_full_double n hn χ)
      change (torsionFullCocycle n hn χ).val σ+(torsionFullCocycle n hn χ).val σ=0 at ht
      rw [hQ σ] at ht
      rw [map_add]
      dsimp [halfDifference] at ht
      apply sub_eq_zero.mp
      calc
        _=(galoisPointHom σ n hn Q-Q)+(galoisPointHom σ n hn Q-Q) := by abel
        _=0 := ht
    obtain ⟨P,hP⟩ := actual_fixed_point_rational n hn (Q+Q) hfixed
    refine ⟨Multiplicative.ofAdd P,?_⟩
    apply Subtype.ext; apply MonoidHom.ext; intro σ
    apply Subtype.ext
    change ((rationalHalvingCocycle n hn P σ).toAdd : Point (algebraMap F Qbar n))=_
    rw [actual_halving_cocycle_evaluate n hn P Q hP.symm]
    exact (hQ σ).symm
  · rintro ⟨P,rfl⟩
    refine ⟨actualHalf n hn (rationalPointMap n hn P.toAdd),?_⟩
    intro σ
    exact actual_halving_cocycle_evaluate n hn P.toAdd _ (actual_half_spec n hn _)

lemma actual_full_connecting_kernel (n : F) (hn : n ≠ 0) :
    (torsionFullClass n hn).ker=rationalCocycleImage n hn := by
  ext χ
  exact actual_full_connecting_exact n hn χ

end ActualTwoDescentFullConnectingExactness318
