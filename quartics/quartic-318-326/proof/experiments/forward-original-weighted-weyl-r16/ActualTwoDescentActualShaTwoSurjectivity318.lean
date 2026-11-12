module
public import ActualTwoDescentActualShaExactKernel318
public section
noncomputable section
namespace ActualTwoDescentActualShaTwoSurjectivity318
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
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentFullHOneTwoSurjectivity318
open ActualTwoDescentTorsionIntoFullCocycles318 ActualTwoDescentCohomologicalSelmer318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentShaRepresentativeIndependence318
open ActualTwoDescentSelmerToActualSha318

/-- Actual Selmer→Sha[2] is surjective: an ACTUAL continuous full cocycle is reduced to E[2] by actual geometric halving. -/
theorem actual_selmer_sha_surjective (n : ℚ) (hn : n ≠ 0) : Function.Surjective (selmerToShaTwo n hn) := by
  rintro ⟨x,hSha,h2⟩
  obtain ⟨z,hz,hlocal⟩ := hSha
  have hx : x.toAdd ∈ continuousFullHOne n hn := ⟨z,hz⟩
  have htwo : x.toAdd+x.toAdd=0 := by
    have h := congrArg Multiplicative.toAdd h2
    simpa only [pow_two,Multiplicative.toAdd_mul,Multiplicative.toAdd_one] using h
  obtain ⟨χ,hχ⟩ := actual_full_hone_two_surjective n hn x.toAdd hx htwo
  have he : fullClassHom n hn (torsionFullCocycle n hn χ)=fullClassHom n hn z := by
    exact (congrArg Multiplicative.toAdd hχ).trans hz.symm
  have hmem : χ ∈ cohomologicalSelmer n hn :=
    (actual_selmer_full_local_iff n hn χ).mpr
      ((actual_local_triviality_class_invariant n hn (torsionFullCocycle n hn χ) z he).mpr hlocal)
  exact ⟨⟨χ,hmem⟩,Subtype.ext hχ⟩

end ActualTwoDescentActualShaTwoSurjectivity318
