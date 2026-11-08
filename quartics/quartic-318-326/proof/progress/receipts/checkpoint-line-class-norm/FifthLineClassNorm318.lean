module
public import LineSheafClass318
public import FifthNormChosenSourceIso318
public section
noncomputable section
namespace FifthLineClassNorm318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318 LineSheafClass318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The actual normed target module with its proven whole-open unit frames. -/
@[expose] def line (L : Line Model) : Line Target where
  object := FifthNormLineObject318.object L.object L.opens L.cover L.frame
  Index := Target
  opens := FifthLineTargetCover318.neighborhood L.object L.opens L.cover L.frame
  cover := FifthLineTargetCover318.cover_top L.object L.opens L.cover L.frame
  frame := FifthNormLineObject318.frame L.object L.opens L.cover L.frame
/-- The construction respects actual source isomorphisms, including independent
choices of original covers and unit frames. -/
def iso {L N : Line Model} (e : L.object ≅ N.object) : (line L).object ≅ (line N).object :=
  FifthNormChosenSourceIso318.iso e L.opens N.opens L.cover N.cover L.frame N.frame
lemma respects {L N : Line Model} (h : Related L N) : Related (line L) (line N) := by
  obtain ⟨e⟩ := h
  exact ⟨iso e⟩
/-- A well-defined map on genuine line-sheaf isomorphism classes. No group,
coherence, base-change or representability structure is asserted here. -/
@[expose] def norm : Class Model → Class Target := Quotient.map line (fun _ _ h => respects h)
lemma norm_classOf (L : Line Model) : norm (classOf L) = classOf (line L) := rfl
lemma presentation_independent {L N : Line Model} (e : L.object ≅ N.object) :
    norm (classOf L) = norm (classOf N) := classOf_eq (iso e)
lemma hom_inv {L N : Line Model} (e : L.object ≅ N.object) :
    (iso e).hom ≫ (iso e).inv = 𝟙 _ := (iso e).hom_inv_id
lemma inv_hom {L N : Line Model} (e : L.object ≅ N.object) :
    (iso e).inv ≫ (iso e).hom = 𝟙 _ := (iso e).inv_hom_id
end FifthLineClassNorm318
