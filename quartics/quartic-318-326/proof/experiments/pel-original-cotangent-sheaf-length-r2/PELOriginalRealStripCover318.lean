module
public import ComplexVerticalStrip318
public import CoverSheetOverlap318
public import PELOriginalGlobalHalfPlaneSheets318
public section
noncomputable section
namespace PELOriginalRealStripCover318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalNormalizedDoubleCover318 PELOriginalHalfPlaneDoubleCover318
open ComplexVerticalStrip318

/-- An entire open real interval (possibly unbounded) avoiding the three
finite branch values of the SAME original normalized cover. -/
structure Interval (i:Fin 4) where
  carrier:Set ℝ
  isOpen:IsOpen carrier
  convex:Convex ℝ carrier
  point:ℝ
  point_mem:point∈carrier
  zero_not:0∉carrier
  one_not:1∉carrier
  parameter_not:(branchParameter i).re∉carrier

variable {i:Fin 4} (J:Interval i)
abbrev Domain:=strip J.carrier
abbrev HalfDomain (upper:Bool):=halfStrip J.carrier upper
local instance : SimplyConnectedSpace J.Domain:=strip_simplyConnected J.convex ⟨J.point,J.point_mem⟩
local instance : LocallyPathConnectedSpace J.Domain:=(strip_open J.isOpen).locallyPathConnectedSpace
local instance (upper:Bool) : SimplyConnectedSpace (J.HalfDomain upper):=
  halfStrip_simplyConnected J.convex ⟨J.point,J.point_mem⟩ upper
local instance (upper:Bool) : LocallyPathConnectedSpace (J.HalfDomain upper):=
  (halfStrip_open J.isOpen upper).locallyPathConnectedSpace
local instance (upper:Bool) : SimplyConnectedSpace (PELOriginalGlobalHalfPlaneSheets318.Half upper):=
  LegendreHalfPlaneAnalyticSheets318.domain_simplyConnected upper
local instance (upper:Bool) : LocallyPathConnectedSpace (PELOriginalGlobalHalfPlaneSheets318.Half upper):=
  (LegendreHalfPlaneAnalyticSheets318.domain_open upper).locallyPathConnectedSpace

@[expose] def image:Set (OnePoint ℂ):=((↑):ℂ→OnePoint ℂ) '' J.Domain
lemma avoids (z:ℂ) (hz:z∈J.Domain) :
    ¬((z:OnePoint ℂ)=∞ ∨ (z:OnePoint ℂ)=(0:ℂ) ∨
      (z:OnePoint ℂ)=(1:ℂ) ∨ (z:OnePoint ℂ)=(branchParameter i:ℂ)) := by
  rintro (h|h|h|h)
  · exact OnePoint.coe_ne_infty z h
  · have he:=OnePoint.coe_injective h
    subst z
    exact J.zero_not hz
  · have he:=OnePoint.coe_injective h
    subst z
    exact J.one_not hz
  · have he:=OnePoint.coe_injective h
    subst z
    exact J.parameter_not hz

/-- The SAME original map covers the entire vertical strip, including its
real seam. Both regular and omitted-inertia original charts are retained. -/
theorem covering : IsCoveringMapOn (normalizedMap i) J.image := by
  have hc:=(PELOriginalCharacterUnramifiedCover318.covering_off_branch i).homeomorph_comp (coordinate i)
  apply hc.mono
  rintro p ⟨z,hz,rfl⟩ hbranch
  have hb:=(actual_branch_values i ((coordinate i).symm (z:OnePoint ℂ))).mp hbranch
  simp only [Homeomorph.apply_symm_apply] at hb
  exact J.avoids z hz hb

@[expose] def basepoint:J.Domain:=⟨(J.point:ℂ),J.point_mem⟩
@[expose] def baseMap:C(J.Domain,OnePoint ℂ):=
  ⟨fun z=>(z.val:OnePoint ℂ),OnePoint.continuous_coe.comp continuous_subtype_val⟩
lemma baseMap_mem (z:J.Domain) : J.baseMap z∈J.image:=⟨z.val,z.property,rfl⟩
abbrev BaseFiber:=SimplyConnectedCoverSheets318.Fiber (normalizedMap i) J.baseMap J.basepoint
@[expose] def sheet (e:J.BaseFiber) : C(J.Domain,CharacterBase i):=
  SimplyConnectedCoverSheets318.sheet (normalizedMap i) J.image J.covering J.baseMap
    J.baseMap_mem J.basepoint e
lemma sheet_projection (e:J.BaseFiber) (z:J.Domain) :
    normalizedMap i (J.sheet e z)=(z.val:OnePoint ℂ):=
  congrFun (SimplyConnectedCoverSheets318.sheet_lifts (normalizedMap i) J.image J.covering
    J.baseMap J.baseMap_mem J.basepoint e) z

@[expose] def toStrip (upper:Bool) : C(J.HalfDomain upper,J.Domain):=
  ⟨fun z=>⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩
@[expose] def toHalf (upper:Bool) : C(J.HalfDomain upper,PELOriginalGlobalHalfPlaneSheets318.Half upper):=
  ⟨fun z=>⟨z.val,z.property.2⟩,continuous_subtype_val.subtype_mk _⟩
@[expose] def sidepoint (upper:Bool) : J.HalfDomain upper:=
  ⟨sidePoint J.point upper,sidePoint_mem J.point_mem upper⟩

/-- A whole-strip sheet matches a single global upper/lower sheet label.
The matching is determined once, not separately above each real point. -/
@[expose] def sideLabels (upper:Bool) : J.BaseFiber≃PELOriginalGlobalHalfPlaneSheets318.BaseFiber i upper:=
  CoverSheetOverlap318.labels (normalizedMap i) J.image nonreal J.covering (covering_nonreal i)
    J.baseMap (PELOriginalGlobalHalfPlaneSheets318.baseMap upper) J.baseMap_mem
    (PELOriginalGlobalHalfPlaneSheets318.baseMap_nonreal upper) J.basepoint
    (PELOriginalGlobalHalfPlaneSheets318.basepoint upper) (J.toStrip upper) (J.toHalf upper)
    (fun _=>rfl) (J.sidepoint upper)

/-- Actual equality on the ENTIRE open half-strip, not only at the chosen
matching point. The same continuous sheet crosses every point of the real
interval, establishing constancy of this upper/lower transition there. -/
theorem sheet_agrees (upper:Bool) (e:J.BaseFiber) (z:J.HalfDomain upper) :
    PELOriginalGlobalHalfPlaneSheets318.sheet i upper (J.sideLabels upper e) (J.toHalf upper z)=
      J.sheet e (J.toStrip upper z) :=
  CoverSheetOverlap318.match_everywhere (normalizedMap i) J.image nonreal J.covering (covering_nonreal i)
    J.baseMap (PELOriginalGlobalHalfPlaneSheets318.baseMap upper) J.baseMap_mem
    (PELOriginalGlobalHalfPlaneSheets318.baseMap_nonreal upper) J.basepoint
    (PELOriginalGlobalHalfPlaneSheets318.basepoint upper) (J.toStrip upper) (J.toHalf upper)
    (fun _=>rfl) (J.sidepoint upper) e z

/-- One fixed permutation between the complete actual upper and lower
base fibers for the entire unbranched real interval. -/
@[expose] def transition : PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true≃
    PELOriginalGlobalHalfPlaneSheets318.BaseFiber i false:=
  (J.sideLabels true).symm.trans (J.sideLabels false)
lemma transition_lift (e:PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true) :
    ∃F:C(J.Domain,CharacterBase i),
      (∀z:J.HalfDomain true,PELOriginalGlobalHalfPlaneSheets318.sheet i true e (J.toHalf true z)=F (J.toStrip true z)) ∧
      (∀z:J.HalfDomain false,PELOriginalGlobalHalfPlaneSheets318.sheet i false (J.transition e) (J.toHalf false z)=F (J.toStrip false z)) := by
  refine ⟨J.sheet ((J.sideLabels true).symm e),?_,?_⟩
  · intro z
    simpa only [Equiv.apply_symm_apply] using J.sheet_agrees true ((J.sideLabels true).symm e) z
  · intro z
    exact J.sheet_agrees false ((J.sideLabels true).symm e) z
end PELOriginalRealStripCover318
