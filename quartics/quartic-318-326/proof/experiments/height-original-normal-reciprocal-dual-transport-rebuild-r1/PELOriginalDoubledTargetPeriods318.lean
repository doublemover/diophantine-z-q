module
public import PELOriginalProducedDoubling318
public section
noncomputable section
namespace PELOriginalDoubledTargetPeriods318
open PELOriginalInvolutionTower318 PELOriginalCharacterQuotient318
open PELOriginalResidualDeckAction318 PELOriginalResidualDeckFibers318
open PELOriginalTorusCoverLift318 ComplexLineLatticeAtlas318
open Set Topology
variable (i:Fin 4)

/-- Translation by ANY genuine target period lifts to one of the
ACTUAL original residual deck transformations, on the entire complex
line. Equality at the origin extends by covering lift uniqueness. -/
theorem target_translation_deck (a:ℂ) (ha:a∈PELOriginalCharacterTorus318.periods i) :
    ∃g:Deck i,∀z,universalLift i (z+a)=g • universalLift i z := by
  have hz:projection (PELOriginalCharacterTorus318.periods i) a=0:=
    QuotientAddGroup.eq_zero_iff.mpr ha
  have hb:toCharacterBase i (universalLift i a)=toCharacterBase i (universalLift i 0):=by
    rw [universalLift_original_projection,universalLift_original_projection,hz,
      show projection (PELOriginalCharacterTorus318.periods i) 0=0 from rfl]
  obtain ⟨g,hg⟩:=(fiber_iff_orbit i (universalLift i a) (universalLift i 0)).mp hb
  have hc:torusMap i ∘ (fun z=>universalLift i (z+a))=
      torusMap i ∘ (fun z=>g • universalLift i z):=by
    funext z
    change torusMap i (universalLift i (z+a))=
      (PELOriginalCharacterTorus318.comparison i).symm (toCharacterBase i (g • universalLift i z))
    rw [deck_over_base]
    change torusMap i (universalLift i (z+a))=torusMap i (universalLift i z)
    rw [universalLift_projection,universalLift_projection]
    change (QuotientAddGroup.mk' (PELOriginalCharacterTorus318.periods i)) (z+a)=
      (QuotientAddGroup.mk' (PELOriginalCharacterTorus318.periods i)) z
    rw [map_add,show (QuotientAddGroup.mk' (PELOriginalCharacterTorus318.periods i)) a=0 from hz,add_zero]
  have h0:universalLift i (0+a)=g • universalLift i 0:=by
    simpa only [zero_add] using hg.symm
  have hh:=(torusMap_covering i).eq_of_comp_eq
    ((universalLift i).continuous.comp (continuous_id.add continuous_const))
    ((PELOriginalResidualDeckHolomorphy318.deck_continuous i g).comp (universalLift i).continuous)
    hc 0 h0
  exact ⟨g,fun z=>congrFun hh z⟩

/-- The actual residual group has exponent TWO, so twice EVERY target
period is a genuine complete source period. Degree four alone would not
imply this; the actual old deck action is used explicitly. -/
theorem double_mem_source (a:ℂ) (ha:a∈PELOriginalCharacterTorus318.periods i) :
    a+a∈PELOriginalInvolutionActualTorus318.periods i := by
  obtain ⟨g,hg⟩:=target_translation_deck i a ha
  apply (ComplexTorusCoverPeriods318.period_iff_center
    (PELOriginalCharacterTorus318.periods i) (torusMap i) (torusMap_covering i)
    (origin i) (origin_over_zero i) (a+a)).mpr
  change universalLift i (a+a)=origin i
  have h0:universalLift i a=g • universalLift i 0:=by
    simpa only [zero_add] using hg 0
  rw [hg a,h0,←mul_smul,deck_square,one_smul,universalLift_origin]

lemma two_zsmul_mem_source (a:PELOriginalCharacterTorus318.periods i) :
    (2:ℤ) • (a:ℂ)∈PELOriginalInvolutionActualTorus318.periods i := by
  simpa only [two_zsmul] using double_mem_source i a.val a.property
end PELOriginalDoubledTargetPeriods318
