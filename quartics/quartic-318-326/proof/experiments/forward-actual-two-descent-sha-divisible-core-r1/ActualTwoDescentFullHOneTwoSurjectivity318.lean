module
public import ActualTwoDescentHalvedFullCocycle318
public section
noncomputable section
namespace ActualTwoDescentFullHOneTwoSurjectivity318
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
open ActualTwoDescentHalvedFullCocycle318

/-- Genuine surjectivity H1_cont(E[2])→H1_cont(E)[2], using actual algebraic-closure halving and no global rational-point assumption. -/
theorem actual_full_hone_two_surjective (n : F) (hn : n ≠ 0) (x : H1 (fullEllipticRep n hn))
    (hx : x ∈ continuousFullHOne n hn) (h2 : x+x=0) :
    ∃ χ : continuousCocycles n, torsionFullClass n hn χ=Multiplicative.ofAdd x := by
  obtain ⟨z,rfl⟩ := hx
  have hzero : fullClassHom n hn (z+z)=0 := by rw [map_add]; exact h2
  obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn (z+z)).mp hzero
  let R := actualHalf n hn Q
  have hR : R+R=Q := actual_half_spec n hn Q
  have ht := actual_halved_full_values n hn z Q R hR hQ
  refine ⟨halvedFullCocycle n hn z R ht,?_⟩
  change Multiplicative.ofAdd (fullClassHom n hn (torsionFullCocycle n hn (halvedFullCocycle n hn z R ht)))=_
  rw [actual_halved_full_cocycle_value,map_sub,actual_full_boundary_zero,sub_zero]

end ActualTwoDescentFullHOneTwoSurjectivity318
