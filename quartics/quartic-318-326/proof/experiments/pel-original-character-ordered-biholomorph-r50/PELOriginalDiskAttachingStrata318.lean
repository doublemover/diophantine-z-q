module
public import PELOriginalOpenTwoCell318
public import PELOriginalEdgeStrata318
public section
noncomputable section
namespace PELOriginalDiskAttachingStrata318
open Set Metric
open PELOriginalPolygonDisk318 PELOriginalDiskCharacteristic318
open PELOriginalDirichletPolygon318 PELActualPolygonHomeomorph318
open PELStrictPolygonExtension318 PELDirichletHeight318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318 PELDirichletIncidence318
open PELOriginalPolygonBoundary318 PELOriginalOpenEdgeDisjoint318
open PELOriginalActualVertexGluing318 PELOriginalProjectiveTangents318
open PELOriginalVertexStratum318 PELOriginalEdgeStrata318 PELUnlevelledComplexBase318
set_option maxHeartbeats 1800000

theorem disk_strict_iff (z : ClosedDisk) :
    strictInequalities (scaledFirst (diskOriginalHomeomorph z).val)
      (scaledSecond (diskOriginalHomeomorph z).val) ↔ z.val∈ball 0 1 := by
  constructor
  · intro hs
    change strictInequalities
      (scaledFirst (polygonInverse (closedDiskPolygonHomeomorph z)).val)
      (scaledSecond (polygonInverse (closedDiskPolygonHomeomorph z)).val) at hs
    rw [(inverse_scaled _).1,(inverse_scaled _).2] at hs
    have hp : (closedDiskPolygonHomeomorph z).val∈interior planePolygon :=
      strict_mem_interior hs
    have hi := Set.mem_image_of_mem diskNormalization hp
    rw [normalization_interior] at hi
    change diskNormalization (diskNormalization.symm z.val)∈ball 0 1 at hi
    simpa only [diskNormalization.apply_symm_apply] using hi
  · exact disk_original_strict z

theorem disk_boundary_iff (z : ClosedDisk) : z.val∈sphere 0 1 ↔
    ¬ strictInequalities (scaledFirst (diskOriginalHomeomorph z).val)
      (scaledSecond (diskOriginalHomeomorph z).val) := by
  rw [disk_strict_iff]
  change dist z.val 0=1 ↔ ¬ dist z.val 0<1
  have hz : dist z.val 0≤1 := z.property
  constructor <;> intro h <;> linarith

theorem strict_side_positive (P : ℝ × ℝ) (hs : strictInequalities P.1 P.2) (e : Fin 28) :
    0<realSideValue e P := by
  have h := hs (selection e).1 (selection e).2.1 (selection e).2.2
  fin_cases e <;>
    norm_num [realSideValue,row,selection,rowFirst,rowSecond,rowConstant,sign] at * <;> linarith

theorem vertex_not_strict (v : Fin 28) :
    ¬ strictInequalities (scaledFirst (vertexPoint v).val) (scaledSecond (vertexPoint v).val) := by
  intro hs
  have heq := vertexPoint_coordinates v
  have hs' : strictInequalities (realPoint (vertex v)).1 (realPoint (vertex v)).2 := by
    rw [←heq]
    exact hs
  obtain ⟨e,_,he⟩ := another_active_side v 0
  have hp := strict_side_positive (realPoint (vertex v)) hs' e
  rw [realSideValue_vertex,he] at hp
  norm_num at hp

theorem edge_not_strict (e : Fin 28) (s : ℝ) (hs0 : 0<s) (hs1 : s<1) :
    ¬ strictInequalities
      (scaledFirst (PELActualOriginalSideGluing318.segmentPoint (start e) (finish e) s hs0.le hs1.le).val)
      (scaledSecond (PELActualOriginalSideGluing318.segmentPoint (start e) (finish e) s hs0.le hs1.le).val) := by
  intro hs
  have heq := PELActualOriginalSideGluing318.segment_coordinates (start e) (finish e) s hs0.le hs1.le
  have hs' : strictInequalities
      (PELRealKleinSideTransport318.realMix (realPoint (vertex (start e)))
        (realPoint (vertex (finish e))) s).1
      (PELRealKleinSideTransport318.realMix (realPoint (vertex (start e)))
        (realPoint (vertex (finish e))) s).2 := by
    rw [←heq]
    exact hs
  have hp := strict_side_positive _ hs' e
  rw [(open_side_active_iff e e s hs0 hs1).mpr rfl] at hp
  exact (lt_irrefl 0) hp

/-- Any original closed-polygon boundary representative comes from the
actual standard attaching sphere of the constructed disk. -/
theorem nonstrict_in_attaching (p : originalDomain)
    (hp : ¬ strictInequalities (scaledFirst p.val) (scaledSecond p.val)) :
    projection p.val∈attachingImage := by
  let z := diskOriginalHomeomorph.symm p
  have hz : z.val∈sphere 0 1 := (disk_boundary_iff z).mpr (by
    simpa only [z,diskOriginalHomeomorph.apply_symm_apply] using hp)
  refine ⟨z,hz,?_⟩
  change projection (diskOriginalHomeomorph z).val=projection p.val
  rw [diskOriginalHomeomorph.apply_symm_apply]

/-- Exact identification of the actual attaching-circle image with the
actual zero/one strata. Neither a combinatorial boundary label nor an
unproved CW attaching condition is supplied as an assumption. -/
theorem attaching_exact_lower_strata : attachingImage=VertexImage ∪ ⋃ e : Fin 28, EdgeImage e := by
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hn := (disk_boundary_iff z).mp hz
    rcases original_point_stratification (diskOriginalHomeomorph z).val
      (diskOriginalHomeomorph z).property with hs | ⟨v,hv⟩ | ⟨e,s,hs0,hs1,he⟩
    · exact False.elim (hn hs)
    · left
      refine ⟨v,?_⟩
      change projection (vertexPoint v).val=projection (diskOriginalHomeomorph z).val
      rw [hv]
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨e,s,hs0,hs1,?_⟩
      change projection _=projection (diskOriginalHomeomorph z).val
      rw [he]
  · rintro (⟨v,hv⟩ | he)
    · rw [←hv]
      exact nonstrict_in_attaching (vertexPoint v) (vertex_not_strict v)
    · obtain ⟨e,s,hs0,hs1,he⟩ := Set.mem_iUnion.mp he
      rw [←he]
      exact nonstrict_in_attaching _ (edge_not_strict e s hs0 hs1)
end PELOriginalDiskAttachingStrata318
