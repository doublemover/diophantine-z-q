module
public import ActualTwoDescentShaRepresentativeIndependence318
public section
noncomputable section
namespace ActualTwoDescentSelmerToActualSha318
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
open ActualTwoDescentTorsionIntoFullCocycles318 ActualTwoDescentFullConnectingExactness318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentShaRepresentativeIndependence318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentCohomologicalSelmer318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- The actual cohomological Selmer condition is exactly local triviality of its LITERAL full elliptic cocycle. -/
lemma actual_selmer_full_local_iff (n : ℚ) (hn : n ≠ 0) (χ : continuousCocycles n) :
    χ ∈ cohomologicalSelmer n hn ↔ EverywhereLocallyTrivial n hn (torsionFullCocycle n hn χ) := by
  have hlocal {L : Type} [Field L] [CharZero L] [DecidableEq L] (f : ℚ →+* L) :
      cocycleRestriction f n hn χ ∈ rationalCocycleImage (f n) (field_map_ne_zero f hn) ↔
      fullClassHom (f n) (field_map_ne_zero f hn)
        (fullCocycleRestriction f n hn (torsionFullCocycle n hn χ))=0 := by
    rw [actual_full_restriction_torsion]
    exact (actual_full_connecting_exact (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ)).symm
  constructor
  · rintro ⟨hR,hp⟩
    exact ⟨(hlocal (algebraMap ℚ ℝ)).mp hR,fun p _ => (hlocal (algebraMap ℚ (ℚ_[p]))).mp (hp p)⟩
  · rintro ⟨hR,hp⟩
    exact ⟨(hlocal (algebraMap ℚ ℝ)).mpr hR,fun p _ => (hlocal (algebraMap ℚ (ℚ_[p]))).mpr (hp p)⟩

def selmerToShaTwo (n : ℚ) (hn : n ≠ 0) : cohomologicalSelmer n hn →* actualShaTwo n hn where
  toFun χ := ⟨torsionFullClass n hn χ,⟨⟨torsionFullCocycle n hn χ,rfl,
    (actual_selmer_full_local_iff n hn χ).mp χ.property⟩,actual_torsion_full_class_two n hn χ⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' χ ψ := Subtype.ext (map_mul _ χ ψ)

end ActualTwoDescentSelmerToActualSha318
