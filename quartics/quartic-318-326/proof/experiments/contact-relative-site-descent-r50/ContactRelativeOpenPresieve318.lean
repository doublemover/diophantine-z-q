module
public import OriginalRelativeSite318
public section
noncomputable section
namespace ContactRelativeOpenPresieve318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T : Scheme} (b : T ⟶ FieldBase t) {ι : Type} (U : ι → T.Opens)

/-- The genuine relative-site sheaf condition on every original open
cover, derived from original relative-class gluing rather than stipulated. -/
lemma isSheafFor (hc : (⊤ : T.Opens) ≤ iSup U) :
    Presieve.IsSheafFor (presheaf (q t))
      (Presieve.ofArrows (fun i => openObject b (U i)) (fun i => openArrow b (U i))) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro c hm
  apply ContactZariskiClassDescent318.matching_unique t b U hc c
  intro i j
  exact hm i j (openObject b (U i ⊓ U j))
    (openInclusion b (show U i ⊓ U j ≤ U i from inf_le_left))
    (openInclusion b (show U i ⊓ U j ≤ U j from inf_le_right))
    (by rw [openInclusion_arrow,openInclusion_arrow])
end ContactRelativeOpenPresieve318
