module
public import PELOriginalGlobalHalfPlaneSheets318
public section
noncomputable section
namespace PELOriginalOpenHalfPlaneSheets318
open Set Topology
open scoped OnePoint
open PELOriginalGlobalHalfPlaneSheets318 LegendreHalfPlaneAnalyticSheets318
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalHalfPlaneDoubleCover318

/-- Each globally lifted original sheet is an actual OPEN EMBEDDING into
the unchanged original character curve, not a topology transported from a
chosen sheet type. Both openness and inverse continuity follow locally
from the proved original covering and exact projection equation. -/
theorem sheet_openEmbedding (i:Fin 4) (upper:Bool) (e:BaseFiber i upper) :
    IsOpenEmbedding (sheet i upper e) := by
  have hc:normalizedMap i ∘ sheet i upper e=baseMap upper := by
    funext z
    exact sheet_projection i upper e z
  have hb:IsOpenEmbedding (baseMap upper):=
    OnePoint.isOpenEmbedding_coe.comp (domain_open upper).isOpenEmbedding_subtypeVal
  have hlocal:IsLocalHomeomorphOn (normalizedMap i)
      (sheet i upper e '' (univ:Set (Half upper))) := by
    apply (covering_nonreal i).isLocalHomeomorphOn.mono
    rintro q ⟨z,_,rfl⟩
    change normalizedMap i (sheet i upper e z)∈nonreal
    rw [sheet_projection]
    exact baseMap_nonreal upper z
  have hs:IsLocalHomeomorph (sheet i upper e) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    apply IsLocalHomeomorphOn.of_comp_left
      (show IsLocalHomeomorphOn (normalizedMap i ∘ sheet i upper e) univ from
        hc.symm ▸ hb.isLocalHomeomorph.isLocalHomeomorphOn) hlocal
    intro z _
    exact (sheet i upper e).continuous.continuousAt
  apply hs.isOpenEmbedding_of_injective
  intro z w h
  have hp:=congrArg (normalizedMap i) h
  rw [sheet_projection,sheet_projection] at hp
  exact Subtype.ext (OnePoint.coe_injective hp)
end PELOriginalOpenHalfPlaneSheets318
