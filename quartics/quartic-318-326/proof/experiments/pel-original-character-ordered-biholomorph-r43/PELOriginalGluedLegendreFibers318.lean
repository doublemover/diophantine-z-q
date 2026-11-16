module
public import PELOriginalGluedLegendreMap318
public section
noncomputable section
namespace PELOriginalGluedLegendreFibers318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open PELOriginalCompatibleLegendreCoordinates318 PELOriginalGluedLegendreMap318
open PELOriginalHalfPlaneSheetTopology318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalRealBranchIntervals318 PELOriginalOpenRealStripSheets318
open LegendreHalfPlaneAnalyticSheets318 LegendreAllBranchTransitions318
open PELOriginalGlobalSheetAlignment318 NormalizedLegendreFieldPoints318

lemma signed_not (b:Bool) (z:ℂ) : signed (!b) z= -signed b z := by
  cases b <;> simp [signed]
lemma targetLabel_not (i:Fin 4) (upper b:Bool) : targetLabel i upper (!b)= !(targetLabel i upper b) := by
  cases upper
  · exact equiv_not (lowerAlignment i) b
  · rfl
lemma value_not (i:Fin 4) (k:Kind) (b:Bool) (z:ℂ) :
    value i (k,!b) z= -value i (k,b) z := by
  cases k with
  | inl upper=>
    change signed (targetLabel i upper (!b)) _= -signed (targetLabel i upper b) _
    rw [targetLabel_not,signed_not]
  | inr j=>exact signed_not b _
lemma polynomial_nonzero_patch (i:Fin 4) (k:Kind) (z:patchDomain i k) :
    polynomial (branchParameter i) z.val≠0 := by
  cases k with
  | inl upper=>exact polynomial_nonzero _ (PELOriginalRealBranchParameters318.branchParameter_im_zero i)
      upper z.val z.property
  | inr j=>exact LegendreRealStripSheets318.polynomial_nonzero_strip ((ordering i).interval j) z.val z.property
lemma value_nonzero (i:Fin 4) (k:Kind) (b:Bool) (z:patchDomain i k) : value i (k,b) z.val≠0 := by
  intro h
  have hh:=value_square i (k,b) z.val
  rw [h,zero_pow (by decide:2≠0)] at hh
  exact polynomial_nonzero_patch i k z hh.symm
lemma value_label_injective (i:Fin 4) (k:Kind) (z:patchDomain i k) :
    Function.Injective (fun b=>value i (k,b) z.val) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · have hn:=value_nonzero i k true z
    have hf:value i (k,false) z.val= -value i (k,true) z.val:=value_not i k true z.val
    rw [hf] at h
    exact False.elim (hn (by linear_combination -h/2))
  · have hn:=value_nonzero i k false z
    have ht:value i (k,true) z.val= -value i (k,false) z.val:=value_not i k false z.val
    rw [ht] at h
    exact False.elim (hn (by linear_combination -h/2))
  · rfl
lemma every_root (i:Fin 4) (k:Kind) (z:patchDomain i k) (y:ℂ)
    (hy:y^2=polynomial (branchParameter i) z.val) : ∃b:Bool,value i (k,b) z.val=y := by
  have hh:y^2=(value i (k,true) z.val)^2:=hy.trans (value_square i (k,true) z.val).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h|h
  · exact ⟨true,h.symm⟩
  · exact ⟨false,(value_not i k true z.val).trans h.symm⟩

/-- Every whole fiber over ANY patch domain is exhausted by the two same
actual source labels. No choice of a new chart for the other point is needed. -/
lemma kind_exhaustive (i:Fin 4) (k:Kind) (z:patchDomain i k) (x:CharacterBase i)
    (hx:normalizedMap i x=(z.val:OnePoint ℂ)) :
    ∃b:Bool,patch i (k,b) z=x := by
  cases k with
  | inl upper=>
    obtain ⟨e,he,_⟩:=original_sheet_exhaustion i upper z x hx
    obtain ⟨b,rfl⟩:=(enumeration i upper).surjective e
    exact ⟨b,he⟩
  | inr j=>
    obtain ⟨e,he⟩:=strip_exhaustive ((ordering i).interval j) z x hx
    obtain ⟨b,rfl⟩:=(enumeration i true).surjective e
    exact ⟨b,he⟩

/-- The glued comparison is injective on the ENTIRE original regular
locus, including real seam points, by exact coordinate and full-fiber data. -/
theorem finiteMap_injective (i:Fin 4) : Function.Injective (finiteMap i) := by
  intro x y h
  have hc:coordinates i x.val=coordinates i y.val:=congrArg Subtype.val h
  obtain ⟨⟨k,b⟩,z,hz⟩:=patches_cover i x.val x.property
  have hyp:normalizedMap i y.val=(z.val:OnePoint ℂ):=by
    rw [←coordinates_projection i y.val y.property,←congrArg Prod.fst hc,←hz,coordinates_patch]
  obtain ⟨c,hc'⟩:=kind_exhaustive i k z y.val hyp
  have hv:value i (k,b) z.val=value i (k,c) z.val:=by
    have hh:=congrArg Prod.snd hc
    rw [←hz,←hc',coordinates_patch,coordinates_patch] at hh
    exact hh
  have hb:b=c:=value_label_injective i k z hv
  apply Subtype.ext
  rw [←hz,←hc',hb]

abbrev Target (i:Fin 4):={p:FinitePoints (branchParameter i)//
  p.val.1≠0 ∧ p.val.1≠1 ∧ p.val.1≠branchParameter i}
lemma finiteMap_regular (i:Fin 4) (x:Regular i) :
    (finiteMap i x).val.1≠0 ∧ (finiteMap i x).val.1≠1 ∧
      (finiteMap i x).val.1≠branchParameter i := by
  rcases x.property with ⟨z,hz,h0,h1,hλ⟩
  have hh:(coordinates i x.val).1=z:=OnePoint.coe_injective
    ((coordinates_projection i x.val x.property).trans hz)
  change (coordinates i x.val).1≠0 ∧ (coordinates i x.val).1≠1 ∧ (coordinates i x.val).1≠branchParameter i
  rw [hh]
  exact ⟨h0,h1,hλ⟩
@[expose] def comparison (i:Fin 4) (x:Regular i) : Target i:=
  ⟨finiteMap i x,finiteMap_regular i x⟩
lemma comparison_continuous (i:Fin 4) : Continuous (comparison i):=
  (finiteMap_continuous i).subtype_mk _

/-- Every ACTUAL finite target point away from the same branch set is
hit. Original projection surjectivity chooses a domain; two genuine
source sheets then realize BOTH roots of the literal target polynomial. -/
theorem comparison_surjective (i:Fin 4) : Function.Surjective (comparison i) := by
  intro p
  obtain ⟨x,hx⟩:=PELOriginalNormalizedDoubleCover318.surjective i (p.val.val.1:OnePoint ℂ)
  have hr:x∈Regular i:=⟨p.val.val.1,hx,p.property.1,p.property.2.1,p.property.2.2⟩
  obtain ⟨⟨k,b⟩,z,hz⟩:=patches_cover i x hr
  have ht:z.val=p.val.val.1:=OnePoint.coe_injective
    ((patch_projection i (k,b) z).symm.trans ((congrArg (normalizedMap i) hz).trans hx))
  have hp:p.val.val.2^2=polynomial (branchParameter i) z.val:=by
    rw [ht]
    exact p.val.property
  obtain ⟨c,hc⟩:=every_root i k z p.val.val.2 hp
  refine ⟨⟨patch i (k,c) z,patch_regular i (k,c) z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change coordinates i (patch i (k,c) z)=p.val.val
  rw [coordinates_patch]
  exact Prod.ext ht hc
lemma comparison_bijective (i:Fin 4) : Function.Bijective (comparison i):=
  ⟨fun _ _ h=>finiteMap_injective i (congrArg Subtype.val h),comparison_surjective i⟩

/-- A genuine bijective map of the WHOLE unbranched original cover onto
the original Legendre finite equation. Inverse continuity is a separate
open-graph statement, not inferred from bijectivity. -/
@[expose] def equivalence (i:Fin 4) : Regular i≃Target i:=
  Equiv.ofBijective (comparison i) (comparison_bijective i)
end PELOriginalGluedLegendreFibers318
