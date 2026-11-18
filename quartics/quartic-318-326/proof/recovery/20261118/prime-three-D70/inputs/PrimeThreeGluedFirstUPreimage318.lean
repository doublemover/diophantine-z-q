module
public import PrimeThreeGluedSecondModification318
public import ThreePieceOpenGluePair318
public section
noncomputable section
namespace PrimeThreeGluedFirstUPreimage318
open AlgebraicGeometry CategoryTheory
open PrimeThreeSecondFirstOverlapBridges318 PrimeThreeGluedSecondModification318
open OriginalPrimeThreeFirstUNativeChart318 PrimeThreeResidualPointChartExclusion318

/-- Typed unchanged-piece inclusion. The explicit finite cases avoid
assuming a vector-indexed scheme family is definitionally the same as
an independently indexed native-chart family. -/
@[expose] def otherPieceInclusion (j : Fin 2) :
    Spec (CommRingCat.of (FirstOther j)) ⟶ gluedSecondModification := by
  fin_cases j
  · exact chartInclusion 1
  · exact chartInclusion 2

instance otherPieceInclusion_openImmersion (j : Fin 2) :
    IsOpenImmersion (otherPieceInclusion j) := by
  fin_cases j <;> dsimp only [otherPieceInclusion] <;> infer_instance

/-- The two gluing arms agree inside the constructed scheme, not only
after mapping to the first blowup. -/
theorem glued_overlap (j : Fin 2) :
    overlapToSecond j ≫ chartInclusion 0 = overlapToOther j ≫ otherPieceInclusion j := by
  have h := ThreePieceOpenGluePair318.pair_inclusions actualTriangle 0 j.succ (by simp)
  fin_cases j <;>
    simpa [actualTriangle, chartInclusion, otherPieceInclusion, PrimeThreeActualGluingTriangle318.inclusion,
      PrimeThreeActualGluingTriangle318.transition] using h

theorem firstU_range : explicitFirstUInclusion.opensRange =
    Proj.basicOpen OriginalPrimeThreeNativeReesProj318.grading
      (OriginalPrimeThreeNativeReesProj318.generator 0) := by
  rw [firstUInclusion_factor, Scheme.Hom.opensRange_comp_of_isIso]
  exact Proj.opensRange_awayι _ _ _ _

instance oldOverlap_openImmersion (j : Fin 2) : IsOpenImmersion (oldOverlapInclusion j) := by
  dsimp only [oldOverlapInclusion]
  infer_instance

theorem oldOverlap_range (j : Fin 2) : (oldOverlapInclusion j).opensRange =
    Proj.basicOpen OriginalPrimeThreeNativeReesProj318.grading
      (OriginalPrimeThreeNativeReesProj318.generator 0) ⊓
    Proj.basicOpen OriginalPrimeThreeNativeReesProj318.grading
      (OriginalPrimeThreeNativeReesProj318.generator j.succ) := by
  rw [oldOverlapInclusion, Proj.opensRange_awayι, Proj.basicOpen_mul]

/-- Exact exhaustion of the old first-U intersection inside each
unchanged chart. Only the already proved native basic-open identities are used. -/
theorem other_point_lifts (j : Fin 2) (y : Spec (CommRingCat.of (FirstOther j)))
    (hy : OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ y ∈
      explicitFirstUInclusion.opensRange) :
    ∃ z, overlapToOther j z = y := by
  have hv : OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ y ∈
      Proj.basicOpen OriginalPrimeThreeNativeReesProj318.grading
        (OriginalPrimeThreeNativeReesProj318.generator j.succ) := by
    rw [← Proj.opensRange_awayι OriginalPrimeThreeNativeReesProj318.grading
      (OriginalPrimeThreeNativeReesProj318.generator j.succ)
        (OriginalPrimeThreeNativeReesProj318.generator_mem j.succ) (by decide)]
    exact ⟨y, rfl⟩
  rw [firstU_range] at hy
  have hz : OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ y ∈
      (oldOverlapInclusion j).opensRange := by
    rw [oldOverlap_range]
    exact ⟨hy, hv⟩
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, ?_⟩
  apply (OriginalPrimeThreeNativeReesProj318.nativeChartInclusion j.succ).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, overlapToOther_toFirstBlowup]
  exact hz

/-- The modified piece is exactly the entire inverse image of the old
first-U open, rather than just an open subset mapping there. -/
theorem firstU_preimage :
    toFirstBlowup ⁻¹ᵁ explicitFirstUInclusion.opensRange = (chartInclusion 0).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy⟩ := actual_pieces_cover x
    subst x
    have hp : PrimeThreeActualGluingTriangle318.pieceToFirst i y ∈
        explicitFirstUInclusion.opensRange := by
      change (chartInclusion i ≫ toFirstBlowup) y ∈ _ at hx
      rwa [chartInclusion_toFirstBlowup] at hx
    fin_cases i
    · exact ⟨y, rfl⟩
    · obtain ⟨z, hz⟩ := other_point_lifts 0 y hp
      refine ⟨overlapToSecond 0 z, ?_⟩
      rw [← Scheme.Hom.comp_apply, glued_overlap, Scheme.Hom.comp_apply, hz]
    · obtain ⟨z, hz⟩ := other_point_lifts 1 y hp
      refine ⟨overlapToSecond 1 z, ?_⟩
      rw [← Scheme.Hom.comp_apply, glued_overlap, Scheme.Hom.comp_apply, hz]
  · rintro ⟨y, rfl⟩
    change (chartInclusion 0 ≫ toFirstBlowup) y ∈ _
    rw [chartInclusion_toFirstBlowup]
    exact ⟨PrimeThreeActualSecondReesProj318.toFirstU y, rfl⟩

/-- Canonical actual base change of the glued morphism over old first-U
is the native relative Rees Proj of the actual residual center. -/
@[expose] def firstUPullbackIso :
    Limits.pullback toFirstBlowup explicitFirstUInclusion ≅
      PrimeThreeActualSecondReesProj318.actualSecondProj :=
  IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst toFirstBlowup explicitFirstUInclusion)
    (chartInclusion 0) (by rw [IsOpenImmersion.range_pullbackFst, firstU_preimage])

@[reassoc] theorem firstUPullbackIso_hom_inclusion :
    firstUPullbackIso.hom ≫ chartInclusion 0 =
      Limits.pullback.fst toFirstBlowup explicitFirstUInclusion :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The canonical second projection is the relative Rees base map
under that isomorphism; the ring/model base is not forgotten. -/
@[reassoc] theorem firstUPullbackIso_hom_toFirstU :
    firstUPullbackIso.hom ≫ PrimeThreeActualSecondReesProj318.toFirstU =
      Limits.pullback.snd toFirstBlowup explicitFirstUInclusion := by
  apply (cancel_mono explicitFirstUInclusion).mp
  rw [Category.assoc]
  change firstUPullbackIso.hom ≫ PrimeThreeActualSecondReesProj318.toFirstBlowup = _
  have h := chartInclusion_toFirstBlowup 0
  change chartInclusion 0 ≫ toFirstBlowup = PrimeThreeActualSecondReesProj318.toFirstBlowup at h
  calc
    firstUPullbackIso.hom ≫ PrimeThreeActualSecondReesProj318.toFirstBlowup =
        firstUPullbackIso.hom ≫ (chartInclusion 0 ≫ toFirstBlowup) :=
      congrArg (fun f => firstUPullbackIso.hom ≫ f) h.symm
    _ = Limits.pullback.fst toFirstBlowup explicitFirstUInclusion ≫ toFirstBlowup := by
      rw [← Category.assoc, firstUPullbackIso_hom_inclusion]
    _ = _ := Limits.pullback.condition

end PrimeThreeGluedFirstUPreimage318
