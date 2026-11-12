module
public import ActualTwoDescentActualSelmerCardinality318
public section
noncomputable section
namespace ActualTwoDescentSelmerObstructionComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentCohomologicalSelmer318 ActualTwoDescentSelmerSquareclassComparison318
open ActualTwoDescentFieldActualCohomologicalImage318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldImageCriterion318 ActualTwoDescentConcreteLocalObstruction318

def selmerRationalInside (n : ℚ) (hn : n ≠ 0) : Subgroup (cohomologicalSelmer n hn) :=
  (rationalCocycleImage n hn).comap (cohomologicalSelmer n hn).subtype
abbrev SelmerObstruction (n : ℚ) (hn : n ≠ 0) := cohomologicalSelmer n hn ⧸ selmerRationalInside n hn

lemma actual_selmer_rational_iff (n : ℚ) (hn : n ≠ 0) (χ : cohomologicalSelmer n hn) :
    χ ∈ selmerRationalInside n hn ↔ selmerSquareclassEquiv n hn χ ∈ rationalImageInside n hn := by
  have h := actual_field_image_criterion n hn (continuousTorsionSquareclasses n hn χ)
  rw [(continuousTorsionSquareclasses n hn).symm_apply_apply] at h
  exact h

lemma actual_selmer_rational_image (n : ℚ) (hn : n ≠ 0) :
    (selmerRationalInside n hn).map (selmerSquareclassEquiv n hn).toMonoidHom=rationalImageInside n hn := by
  ext z
  constructor
  · rintro ⟨χ,hχ,rfl⟩
    exact (actual_selmer_rational_iff n hn χ).mp hχ
  · intro hz
    refine ⟨(selmerSquareclassEquiv n hn).symm z,?_,(selmerSquareclassEquiv n hn).apply_symm_apply z⟩
    apply (actual_selmer_rational_iff n hn _).mpr
    rw [(selmerSquareclassEquiv n hn).apply_symm_apply]
    exact hz

/-- Genuine Selmer modulo actual rational image is the original concrete obstruction; no Sha identification is assumed. -/
def selmerObstructionEquiv (n : ℚ) (hn : n ≠ 0) : SelmerObstruction n hn ≃* LocalObstruction n hn :=
  QuotientGroup.congr (selmerRationalInside n hn) (rationalImageInside n hn)
    (selmerSquareclassEquiv n hn) (actual_selmer_rational_image n hn)

lemma actual_selmer_obstruction_card (n : ℚ) (hn : n ≠ 0) :
    Nat.card (SelmerObstruction n hn)=Nat.card (LocalObstruction n hn) :=
  Nat.card_congr (selmerObstructionEquiv n hn).toEquiv

end ActualTwoDescentSelmerObstructionComparison318
