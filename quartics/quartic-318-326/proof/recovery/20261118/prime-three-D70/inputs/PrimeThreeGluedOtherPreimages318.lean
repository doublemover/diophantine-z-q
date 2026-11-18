module
public import PrimeThreeGluedOtherBaseLifts318
public section
noncomputable section
namespace PrimeThreeGluedOtherPreimages318
open AlgebraicGeometry CategoryTheory
open PrimeThreeSecondFirstOverlapBridges318 PrimeThreeGluedSecondModification318
open PrimeThreeGluedFirstUPreimage318 PrimeThreeGluedOtherBaseLifts318
open PrimeThreeUnchangedVWOverlap318

/-- The entire inverse image of either unchanged first V/W open is its
designated glued piece. This also excludes extra modification points over it. -/
theorem other_preimage (j : Fin 2) :
    toFirstBlowup ⁻¹ᵁ (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ).opensRange =
      (otherPieceInclusion j).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy⟩ := actual_pieces_cover x
    subst x
    have hp : PrimeThreeActualGluingTriangle318.pieceToFirst i y ∈
        (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ).opensRange := by
      change (chartInclusion i ≫ toFirstBlowup) y ∈ _ at hx
      rwa [chartInclusion_toFirstBlowup] at hx
    fin_cases i
    · obtain ⟨z, hz⟩ := second_point_lifts j y hp
      refine ⟨overlapToOther j z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← glued_overlap, Scheme.Hom.comp_apply, hz]
    · fin_cases j
      · exact ⟨y, rfl⟩
      · obtain ⟨z, hz⟩ := v_point_lifts_to_vw y hp
        refine ⟨vwToW z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← glued_vw, Scheme.Hom.comp_apply, hz]
    · fin_cases j
      · obtain ⟨z, hz⟩ := w_point_lifts_to_vw y hp
        refine ⟨vwToV z, ?_⟩
        rw [← Scheme.Hom.comp_apply, glued_vw, Scheme.Hom.comp_apply, hz]
      · exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    change (otherPieceInclusion j ≫ toFirstBlowup) y ∈ _
    fin_cases j
    · change (chartInclusion 1 ≫ toFirstBlowup) y ∈ _
      rw [chartInclusion_toFirstBlowup]
      exact ⟨y, rfl⟩
    · change (chartInclusion 2 ≫ toFirstBlowup) y ∈ _
      rw [chartInclusion_toFirstBlowup]
      exact ⟨y, rfl⟩

/-- Canonical base-change isomorphism to the unchanged native first chart. -/
@[expose] def otherPullbackIso (j : Fin 2) :
    Limits.pullback toFirstBlowup
      (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ) ≅
        Spec (CommRingCat.of (FirstOther j)) :=
  IsOpenImmersion.isoOfRangeEq
    (Limits.pullback.fst toFirstBlowup (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ))
    (otherPieceInclusion j) (by rw [IsOpenImmersion.range_pullbackFst, other_preimage])

@[reassoc] theorem otherPullbackIso_hom_inclusion (j : Fin 2) :
    (otherPullbackIso j).hom ≫ otherPieceInclusion j =
      Limits.pullback.fst toFirstBlowup
        (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- This isomorphism is the actual second pullback projection. Thus the
glued modification is literally unchanged over each old V/W base chart. -/
theorem otherPullbackIso_hom (j : Fin 2) :
    (otherPullbackIso j).hom = Limits.pullback.snd toFirstBlowup
      (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ) := by
  apply (cancel_mono (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ)).mp
  have h : otherPieceInclusion j ≫ toFirstBlowup =
      OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ := by
    fin_cases j
    · exact chartInclusion_toFirstBlowup 1
    · exact chartInclusion_toFirstBlowup 2
  calc
    (otherPullbackIso j).hom ≫ OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ =
        (otherPullbackIso j).hom ≫ (otherPieceInclusion j ≫ toFirstBlowup) :=
      congrArg (fun f => (otherPullbackIso j).hom ≫ f) h.symm
    _ = Limits.pullback.fst toFirstBlowup
        (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ) ≫ toFirstBlowup := by
      rw [← Category.assoc, otherPullbackIso_hom_inclusion]
    _ = _ := Limits.pullback.condition

instance other_base_projection_isIso (j : Fin 2) :
    IsIso (Limits.pullback.snd toFirstBlowup
      (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ)) := by
  rw [← otherPullbackIso_hom]
  infer_instance

end PrimeThreeGluedOtherPreimages318
