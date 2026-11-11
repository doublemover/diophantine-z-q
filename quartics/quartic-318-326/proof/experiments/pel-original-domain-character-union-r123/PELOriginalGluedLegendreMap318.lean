module
public import PELOriginalRegularCoverPatches318
public import PELOriginalCommonLegendreBase318
public section
noncomputable section
namespace PELOriginalGluedLegendreMap318
open Set Topology
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open PELOriginalCompatibleLegendreCoordinates318
open NormalizedLegendreFieldPoints318

/-- A coordinate representative is chosen only to DEFINE the glued map.
Compatibility below proves independence of ALL representatives. -/
@[expose] def representative (i:Fin 4) (x:CharacterBase i) (h:x∈Regular i) :
    Σk:Index,patchDomain i k.1:=
  ⟨(patches_cover i x h).choose,(patches_cover i x h).choose_spec.choose⟩
lemma representative_eq (i:Fin 4) (x:CharacterBase i) (h:x∈Regular i) :
    patch i (representative i x h).1 (representative i x h).2=x:=
  (patches_cover i x h).choose_spec.choose_spec

/-- The ACTUAL glued finite coordinates on the original curve. The
irrelevant value outside the regular locus is never claimed continuous. -/
@[expose] def coordinates (i:Fin 4) (x:CharacterBase i) : ℂ×ℂ:=
  if h:x∈Regular i then
    let r:=representative i x h
    (r.2.val,value i r.1 r.2.val)
  else (0,0)

/-- All whole-halfplane and whole-strip formulas hold for the SAME glued
map, so the arbitrary representative used to define it has disappeared. -/
theorem coordinates_patch (i:Fin 4) (k:Index) (z:patchDomain i k.1) :
    coordinates i (patch i k z)=(z.val,value i k z.val) := by
  rw [coordinates,dif_pos (patch_regular i k z)]
  let r:=representative i (patch i k z) (patch_regular i k z)
  have he:patch i r.1 r.2=patch i k z:=representative_eq i _ _
  have hc:r.2.val=z.val:=by
    have hh:=congrArg (normalizedMap i) he
    rw [patch_projection,patch_projection] at hh
    exact OnePoint.coe_injective hh
  exact Prod.ext hc (compatible i r.1 k r.2 z he)

lemma coordinates_projection (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    ((coordinates i x).1:OnePoint ℂ)=normalizedMap i x := by
  obtain ⟨k,z,rfl⟩:=patches_cover i x hx
  rw [coordinates_patch,patch_projection]
lemma coordinates_equation (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    (coordinates i x).2^2=LegendreHalfPlaneAnalyticSheets318.polynomial
      (branchParameter i) (coordinates i x).1 := by
  obtain ⟨k,z,rfl⟩:=patches_cover i x hx
  rw [coordinates_patch]
  exact value_square i k z.val

/-- Continuity is proved in the UNCHANGED original topology using the
actual open sheets and the compatible analytic coordinate formulas. -/
theorem coordinates_continuous (i:Fin 4) : ContinuousOn (coordinates i) (Regular i) := by
  intro x hx
  obtain ⟨k,z,rfl⟩:=patches_cover i x hx
  have hc:Continuous ((coordinates i) ∘ patch i k):=by
    have hh:((coordinates i) ∘ patch i k)=fun z:patchDomain i k.1=>(z.val,value i k z.val):=by
      funext w
      exact coordinates_patch i k w
    rw [hh]
    exact continuous_subtype_val.prodMk ((value_analytic i k).continuousOn.domRestrict)
  have hlocal:ContinuousOn (coordinates i) (range (patch i k)):=by
    have hh:=((patch_open i k).isEmbedding.isInducing.continuousOn_image_iff
      (s:=univ) (g:=coordinates i)).mpr hc.continuousOn
    simpa only [image_univ] using hh
  exact ((hlocal _ (mem_range_self z)).continuousAt
    ((patch_open i k).isOpen_range.mem_nhds (mem_range_self z))).continuousWithinAt

/-- Holomorphic coordinates in EVERY genuine original open source sheet,
including sheets through every unbranched real point. -/
theorem coordinates_chart_holomorphic (i:Fin 4) (k:Index) :
    ∃F:ℂ→ℂ×ℂ,AnalyticOnNhd ℂ F (patchDomain i k.1) ∧
      ∀z:patchDomain i k.1,F z.val=coordinates i (patch i k z) := by
  refine ⟨fun z=>(z,value i k z),?_,?_⟩
  · intro z hz
    exact analyticAt_id.prod (value_analytic i k z hz)
  · intro z
    exact (coordinates_patch i k z).symm

/-- The glued map lands in the ACTUAL original finite Legendre equation,
not an abstract double cover with the same branch cardinalities. -/
@[expose] def finiteMap (i:Fin 4) (x:Regular i) : FinitePoints (branchParameter i):=
  ⟨coordinates i x.val,coordinates_equation i x.val x.property⟩
lemma finiteMap_continuous (i:Fin 4) : Continuous (finiteMap i):=
  (coordinates_continuous i).domRestrict.subtype_mk _

/-- The complete genuine Scheme-valued base square on the WHOLE regular
original locus, including the entire real seams. -/
theorem scheme_projection (i:Fin 4) (x:Regular i) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (some (finiteMap i x)))=
        PELOriginalCommonLegendreBase318.originalProjection i x.val := by
  rw [NormalizedLegendreFiniteProjection318.finite_projection,
    PELOriginalCommonLegendreBase318.original_projection_coordinate]
  exact congrArg ProjectiveLineComplexSchemePoints318.spherePoint
    (coordinates_projection i x.val x.property)

/-- The globally glued comparison retains EXACTLY the adjusted whole
halfplane formulas, not only agreement away from a set of measure zero. -/
theorem halfplane_restriction (i:Fin 4) (upper b:Bool)
    (z:PELOriginalGlobalHalfPlaneSheets318.Half upper) :
    coordinates i (sourceHalf i upper b z)=(z.val,halfValue i upper b z.val):=
  coordinates_patch i (.inl upper,b) z
/-- Every old upper/lower pair extends through the entire actual strip
with the same glued map and the already constructed target continuation. -/
theorem real_strip_restriction (i:Fin 4) (j:Fin 4) (b:Bool)
    (z:((PELOriginalRealBranchIntervals318.ordering i).interval j).Domain) :
    coordinates i (sourceStrip i j b z)=(z.val,stripValue i j b z.val):=
  coordinates_patch i (.inr j,b) z
end PELOriginalGluedLegendreMap318
