module
public import PELOriginalAllBranchTransitions318
public section
noncomputable section
namespace PELOriginalOpenRealStripSheets318
open Set Topology
open scoped OnePoint
open PELOriginalRealStripCover318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
variable {i:Fin 4} (J:Interval i)
local instance : SimplyConnectedSpace J.Domain:=
  ComplexVerticalStrip318.strip_simplyConnected J.convex ⟨J.point,J.point_mem⟩
local instance : LocallyPathConnectedSpace J.Domain:=
  (ComplexVerticalStrip318.strip_open J.isOpen).locallyPathConnectedSpace

/-- Every whole-strip original lift is an open embedding in the UNCHANGED
original character curve topology. The actual normalized projection is
its base coordinate, and original covering local openness supplies openness. -/
theorem original_sheet_open (e:J.BaseFiber) : IsOpenEmbedding (J.sheet e) := by
  have hc:normalizedMap i ∘ J.sheet e=J.baseMap:=by funext z;exact J.sheet_projection e z
  have hb:IsOpenEmbedding J.baseMap:=OnePoint.isOpenEmbedding_coe.comp
    (ComplexVerticalStrip318.strip_open J.isOpen).isOpenEmbedding_subtypeVal
  have hlocal:IsLocalHomeomorphOn (normalizedMap i) (J.sheet e '' (univ:Set J.Domain)):=by
    apply J.covering.isLocalHomeomorphOn.mono
    rintro x ⟨z,_,rfl⟩
    change normalizedMap i (J.sheet e z)∈J.image
    rw [J.sheet_projection]
    exact ⟨z.val,z.property,rfl⟩
  have hs:IsLocalHomeomorph (J.sheet e):=by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    apply IsLocalHomeomorphOn.of_comp_left
      (show IsLocalHomeomorphOn (normalizedMap i ∘ J.sheet e) univ from
        hc.symm ▸ hb.isLocalHomeomorph.isLocalHomeomorphOn) hlocal
    intro z _
    exact (J.sheet e).continuous.continuousAt
  apply hs.isOpenEmbedding_of_injective
  intro z w h
  have hh:=congrArg (normalizedMap i) h
  rw [J.sheet_projection,J.sheet_projection] at hh
  exact Subtype.ext (OnePoint.coe_injective hh)

/-- Label the strip sheets by the SAME complete global upper base fiber.
Their labels on the lower side are the actual transition, not chosen anew. -/
@[expose] def stripSheet (e:BaseFiber i true) : C(J.Domain,CharacterBase i):=
  J.sheet ((J.sideLabels true).symm e)
@[expose] def stripImage (e:BaseFiber i true) : Set (CharacterBase i):=range (stripSheet J e)
lemma stripSheet_open (e:BaseFiber i true) : IsOpenEmbedding (stripSheet J e):=
  original_sheet_open J _
lemma stripImage_open (e:BaseFiber i true) : IsOpen (stripImage J e):=(stripSheet_open J e).isOpen_range
lemma strip_projection (e:BaseFiber i true) (z:J.Domain) :
    normalizedMap i (stripSheet J e z)=(z.val:OnePoint ℂ):=J.sheet_projection _ z

lemma strip_exhaustive (z:J.Domain) (x:CharacterBase i) (hx:normalizedMap i x=(z.val:OnePoint ℂ)) :
    ∃e:BaseFiber i true,stripSheet J e z=x := by
  obtain ⟨d,hd⟩:=SimplyConnectedCoverSheets318.sheet_exhaustive (normalizedMap i) J.image J.covering
    J.baseMap J.baseMap_mem J.basepoint z x hx
  refine ⟨J.sideLabels true d,?_⟩
  simpa only [stripSheet,Equiv.symm_apply_apply] using hd
lemma strip_upper (e:BaseFiber i true) (z:J.HalfDomain true) :
    stripSheet J e (J.toStrip true z)=sheet i true e (J.toHalf true z) := by
  simpa only [stripSheet,Equiv.apply_symm_apply] using
    (J.sheet_agrees true ((J.sideLabels true).symm e) z).symm
lemma strip_lower (e:BaseFiber i true) (z:J.HalfDomain false) :
    stripSheet J e (J.toStrip false z)=sheet i false (J.transition e) (J.toHalf false z):=
  (J.sheet_agrees false ((J.sideLabels true).symm e) z).symm

/-- Any overlap with an old halfplane sheet determines the SAME label
at every point. The equality is derived by original projection followed
by whole-fiber sheet injectivity, not assumed gluing compatibility. -/
lemma overlap_label (upper:Bool) (e:BaseFiber i true) (f:BaseFiber i upper)
    (z:J.Domain) (w:Half upper) (he:stripSheet J e z=sheet i upper f w) :
    f=J.sideLabels upper ((J.sideLabels true).symm e) := by
  have hcoord:z.val=w.val:=by
    have hh:=congrArg (normalizedMap i) he
    rw [strip_projection,sheet_projection] at hh
    exact OnePoint.coe_injective hh
  let v:J.HalfDomain upper:=⟨z.val,z.property,hcoord.symm ▸ w.property⟩
  have hw:J.toHalf upper v=w:=Subtype.ext hcoord
  have hz:J.toStrip upper v=z:=Subtype.ext rfl
  apply sheets_never_meet i upper w
  have hh:=J.sheet_agrees upper ((J.sideLabels true).symm e) v
  rw [hw,hz] at hh
  exact he.symm.trans hh.symm
end PELOriginalOpenRealStripSheets318
