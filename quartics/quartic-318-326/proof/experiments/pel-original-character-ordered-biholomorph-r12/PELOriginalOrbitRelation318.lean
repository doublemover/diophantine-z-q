module
public import PELOriginalActualVertexGluing318
public import PELOriginalBoundaryAction318
public section
noncomputable section
namespace PELOriginalOrbitRelation318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELJointNormOneAction318
open PELDirichletSidePairingData318 PELDirichletVertexCycles318
open PELOriginalDirichletPolygon318 PELOriginalSideQuotient318
open PELOriginalProjectiveTangents318 PELRealProjectiveDifferential318
open PELActualOriginalSideGluing318 PELRealKleinSideTransport318
open PELOriginalAllUnitMinimum318 PELOriginalInteriorUniqueness318
open PELOriginalActualVertexGluing318 PELOriginalBoundaryAction318
set_option maxHeartbeats 1800000

/-- Equality of heights for ANY two polygon representatives in one original
orbit forces the exact original-unit multiplier1. -/
theorem orbit_multiplier_one (x y : originalDomain) (u : normOneUnits)
    (hu : u • x.val=y.val) :
    denominator (realMatrix ((u.val:order):B)) (scaledFirst x.val,scaledSecond x.val)=1 := by
  have hh := polygon_orbit_height x.val u x.property (by rw [hu]; exact y.property)
  rw [original_height_multiplier] at hh
  nlinarith [height_pos x.val]

/-- EXHAUSTION of every original orbit identification by genuine original
side gluing. Strict points, literal vertices and open real edges are all
covered by the proved full-domain stratification, not separate assumptions. -/
theorem polygon_orbit_quotient (x y : originalDomain) (u : normOneUnits)
    (hu : u • x.val=y.val) : polygonProjection x=polygonProjection y := by
  have hd := orbit_multiplier_one x y u hu
  rcases original_point_stratification x.val x.property with
    hs | ⟨v,hv⟩ | ⟨e,s,hs0,hs1,he⟩
  · have hi := strict_representative_unique x.val u hs (by rw [hu]; exact y.property)
    have hxy : x=y := Subtype.ext (hi.symm.trans hu)
    rw [hxy]
  · have hx : x=vertexPoint v := Subtype.ext hv
    subst x
    rw [vertexPoint_coordinates] at hd
    obtain ⟨w,hw,himage⟩ := original_vertex_action u v (vertexPoint v).val
      (vertexPoint_coordinates v) hd
    rw [hu] at himage
    have hy : y=vertexPoint w := Subtype.ext
      (scaled_injective (himage.trans (vertexPoint_coordinates w).symm))
    rw [hy]
    exact same_class_quotient v w hw.symm
  · have hx : x=segmentPoint (start e) (finish e) s hs0.le hs1.le := Subtype.ext he
    subst x
    rw [segment_coordinates] at hd
    rcases original_edge_action u e s hs0 hs1 hd
      (segmentPoint (start e) (finish e) s hs0.le hs1.le).val with hi | hside
    · have hy : y=segmentPoint (start e) (finish e) s hs0.le hs1.le :=
        Subtype.ext (hu.symm.trans hi)
      rw [hy]
    · have hy : y=segmentPoint (imageStart e) (imageFinish e) s hs0.le hs1.le :=
        Subtype.ext (hu.symm.trans (hside.trans (actual_unit_side e s hs0.le hs1.le)))
      rw [hy]
      exact original_paired_side e s hs0.le hs1.le
end PELOriginalOrbitRelation318
