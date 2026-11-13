module
public import PELOriginalCompatibleLegendreCoordinates318
public section
noncomputable section
namespace PELOriginalRegularCoverPatches318
open Set Topology
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalRealBranchIntervals318 PELOriginalRealStripCover318
open PELOriginalGlobalHalfPlaneSheets318 PELOriginalHalfPlaneSheetTopology318
open PELOriginalOpenRealStripSheets318 PELOriginalCompatibleLegendreCoordinates318
open LegendreHalfPlaneAnalyticSheets318

abbrev Kind:=Bool⊕Fin 4
abbrev Index:=Kind×Bool
@[expose] def patchDomain (i:Fin 4) : Kind→Set ℂ
  | .inl upper=>domain upper
  | .inr j=>((ordering i).interval j).Domain
@[expose] def patch (i:Fin 4) (k:Index) : (patchDomain i k.1)→CharacterBase i:=
  match k.1 with
  | .inl upper=>sourceHalf i upper k.2
  | .inr j=>sourceStrip i j k.2
@[expose] def value (i:Fin 4) (k:Index) : ℂ→ℂ:=
  match k.1 with
  | .inl upper=>halfValue i upper k.2
  | .inr j=>stripValue i j k.2
lemma patch_projection (i:Fin 4) (k:Index) (z:patchDomain i k.1) :
    normalizedMap i (patch i k z)=(z.val:OnePoint ℂ) := by
  rcases k with ⟨upper|j,b⟩
  · exact PELOriginalGlobalHalfPlaneSheets318.sheet_projection i upper _ z
  · exact strip_projection _ _ z
lemma patch_open (i:Fin 4) (k:Index) : IsOpenEmbedding (patch i k) := by
  rcases k with ⟨upper|j,b⟩
  · exact PELOriginalOpenHalfPlaneSheets318.sheet_openEmbedding i upper _
  · exact stripSheet_open _ _
lemma value_analytic (i:Fin 4) (k:Index) : AnalyticOnNhd ℂ (value i k) (patchDomain i k.1) := by
  rcases k with ⟨upper|j,b⟩
  · exact halfValue_analytic i upper b
  · exact stripValue_analytic i j b
lemma value_square (i:Fin 4) (k:Index) (z:ℂ) :
    value i k z^2=polynomial (branchParameter i) z := by
  rcases k with ⟨upper|j,b⟩
  · exact halfValue_square i upper b z
  · exact stripValue_square i j b z

lemma same_half (upper lower:Bool) (z:ℂ) (hu:z∈domain upper) (hl:z∈domain lower) : upper=lower := by
  cases upper <;> cases lower <;> simp_all [domain,side] <;> linarith
lemma gap_unique (i:Fin 4) (j k:Fin 4) (x:ℝ)
    (hj:x∈(ordering i).gap j) (hk:x∈(ordering i).gap k) : j=k := by
  have h0:=(ordering i).lo_lt_mid
  have h1:=(ordering i).mid_lt_hi
  fin_cases j <;> fin_cases k <;> simp_all [PELOriginalRealBranchIntervals318.gap] <;> linarith

lemma strip_label_injective (i:Fin 4) (j:Fin 4) (z:((ordering i).interval j).Domain) :
    Function.Injective (fun b=>sourceStrip i j b z) := by
  let J:Interval i:=(ordering i).interval j
  letI : SimplyConnectedSpace J.Domain:=ComplexVerticalStrip318.strip_simplyConnected J.convex
    ⟨J.point,J.point_mem⟩
  letI : LocallyPathConnectedSpace J.Domain:=(ComplexVerticalStrip318.strip_open J.isOpen).locallyPathConnectedSpace
  intro b c h
  apply (enumeration i true).injective
  apply (J.sideLabels true).symm.injective
  exact SimplyConnectedCoverSheets318.sheet_injective_at (normalizedMap i) J.image J.covering
    J.baseMap J.baseMap_mem J.basepoint z h

/-- ALL actual chart overlaps have identical target y coordinate. The
mixed case uses the proved geometric alignment. Other cases use actual
fiber injectivity or disjoint real gaps, never a transported topology. -/
theorem compatible (i:Fin 4) (k l:Index)
    (z:patchDomain i k.1) (w:patchDomain i l.1) (h:patch i k z=patch i l w) :
    value i k z.val=value i l w.val := by
  have hc:z.val=w.val:=by
    have hh:=congrArg (normalizedMap i) h
    rw [patch_projection,patch_projection] at hh
    exact OnePoint.coe_injective hh
  rcases k with ⟨upper|j,b⟩ <;> rcases l with ⟨lower|k,c⟩
  · have hu:upper=lower:=same_half upper lower z.val z.property (hc.symm ▸ w.property)
    subst lower
    have hz:z=w:=Subtype.ext hc
    subst w
    have hb:b=c:=(enumeration i upper).injective (sheets_never_meet i upper z h)
    subst c
    rfl
  · exact (strip_half_compatible i k upper c b w z h.symm).symm
  · exact strip_half_compatible i j lower b c z w h
  · have hj:j=k:=gap_unique i j k z.val.re z.property
      (show z.val.re∈(ordering i).gap k from hc.symm ▸ w.property)
    subst k
    have hz:z=w:=Subtype.ext hc
    subst w
    have hb:b=c:=strip_label_injective i j z h
    subst c
    rfl

/-- The exact finite unbranched original locus; infinity and all three
finite branch points are excluded, and nothing else is removed. -/
@[expose] def Regular (i:Fin 4) : Set (CharacterBase i):=
  {x|∃z:ℂ,normalizedMap i x=(z:OnePoint ℂ) ∧ z≠0 ∧ z≠1 ∧ z≠branchParameter i}
lemma patch_regular (i:Fin 4) (k:Index) (z:patchDomain i k.1) : patch i k z∈Regular i := by
  have hn:polynomial (branchParameter i) z.val≠0:=by
    rcases k with ⟨upper|j,b⟩
    · exact polynomial_nonzero _ (branchParameter_im_zero i) upper z.val z.property
    · exact LegendreRealStripSheets318.polynomial_nonzero_strip ((ordering i).interval j) z.val z.property
  refine ⟨z.val,patch_projection i k z,?_,?_,?_⟩
  all_goals
    intro h
    apply hn
    simp [polynomial,h]

/-- The open sheet patches cover EVERY point of this original locus. -/
theorem patches_cover (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    ∃k:Index,∃z:patchDomain i k.1,patch i k z=x := by
  rcases hx with ⟨z,hz,h0,h1,hλ⟩
  have lift_half:∀upper:Bool,z∈domain upper→∃k:Index,∃w:patchDomain i k.1,patch i k w=x:=by
    intro upper hu
    obtain ⟨e,he,_⟩:=original_sheet_exhaustion i upper ⟨z,hu⟩ x hz
    obtain ⟨b,rfl⟩:=(enumeration i upper).surjective e
    exact ⟨(.inl upper,b),⟨z,hu⟩,he⟩
  by_cases hp:0<z.im
  · exact lift_half true hp
  by_cases hn:z.im<0
  · exact lift_half false (by simpa [domain,side] using hn)
  have him:z.im=0:=le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
  have hzre:(z.re:ℂ)=z:=by ext <;> simp [him]
  have hav:¬(z.re=0 ∨ z.re=1 ∨ z.re=(branchParameter i).re):=by
    rintro (h|h|h)
    · apply h0;rw [←hzre,h];rfl
    · apply h1;rw [←hzre,h];rfl
    · apply hλ;rw [←hzre,h,←branchParameter_eq_real]
  obtain ⟨j,hj⟩:=(ordering i).gaps_cover z.re hav
  obtain ⟨e,he⟩:=strip_exhaustive ((ordering i).interval j) ⟨z,hj⟩ x hz
  obtain ⟨b,rfl⟩:=(enumeration i true).surjective e
  exact ⟨(.inr j,b),⟨z,hj⟩,he⟩
lemma regular_open (i:Fin 4) : IsOpen (Regular i) := by
  have hh:Regular i=⋃k:Index,range (patch i k):=by
    ext x
    constructor
    · intro hx
      obtain ⟨k,z,hz⟩:=patches_cover i x hx
      exact mem_iUnion.mpr ⟨k,⟨z,hz⟩⟩
    · intro hx
      obtain ⟨k,z,rfl⟩:=mem_iUnion.mp hx
      exact patch_regular i k z
  rw [hh]
  exact isOpen_iUnion fun k=>(patch_open i k).isOpen_range
end PELOriginalRegularCoverPatches318
