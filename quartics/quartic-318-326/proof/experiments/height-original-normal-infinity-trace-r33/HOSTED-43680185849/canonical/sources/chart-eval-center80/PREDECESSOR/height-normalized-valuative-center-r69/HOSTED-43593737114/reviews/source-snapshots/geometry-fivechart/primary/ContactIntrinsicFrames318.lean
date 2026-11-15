module
public import ContactIntrinsicDifferentials318
public import ContactDifferentialFrames318
public import InvariantChartCover318
public section
noncomputable section
namespace ContactIntrinsicFrames318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

abbrev BranchRing (i : Fin 4) := Localization.Away (SourceDenominatorCover318.denominator c i)
@[expose] def branchEmbedding (i : Fin 4) : Spec (CommRingCat.of (BranchRing c i)) ⟶
    ContactGlobalSmooth318.Model c :=
  Spec.map (CommRingCat.ofHom (algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i))) ≫
    SourceGlobalAffine318.chartEmbedding c

instance branchEmbedding_open (i : Fin 4) : IsOpenImmersion (branchEmbedding c i) :=
  @IsOpenImmersion.comp _ _ _ _ _
    (IsOpenImmersion.of_isLocalization (SourceDenominatorCover318.denominator c i))
    (SourceGlobalAffine318.chartEmbedding_open c)

theorem branch_structure (i : Fin 4) :
    branchEmbedding c i ≫ ContactIntrinsicDifferentials318.structureMap c =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (BranchRing c i))) := by
  unfold branchEmbedding ContactIntrinsicDifferentials318.structureMap
  rw [Category.assoc,SourceGlobalAffine318.chartEmbedding_over_Q,←Spec.map_comp]
  congr 1

/-- The actual canonical differential sheaf is free on each actual branch
open, using the ramified root coordinate rather than the singular t-coordinate. -/
@[expose] def branchFrame (i : Fin 4) :
    (ContactIntrinsicDifferentials318.omega c).restrict (branchEmbedding c i) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (BranchRing c i))).ringCatSheaf :=
  (IntrinsicChartNormalization318.iso (branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (branch_structure c i)).symm ≪≫
      AffineDifferentialSheaf318.frameIso (ContactDifferentialFrames318.sourceLocalizationFrame c i)

@[expose] def infinityFrame :
    (ContactIntrinsicDifferentials318.omega c).restrict (InfinityGlobalScheme318.chartEmbedding c) ≅
      SheafOfModules.unit (ReciprocalInfinityNormalization318.neighborhood c).ringCatSheaf :=
  (ContactIntrinsicDifferentials318.infinityIso c).symm ≪≫
    AffineDifferentialSheaf318.frameIso (ContactDifferentialFrames318.infinityFrame c)

theorem frames_cover (x : ContactGlobalSmooth318.Model c) :
    (∃ i, ∃ q, branchEmbedding c i q=x) ∨
      (∃ q, InfinityGlobalScheme318.chartEmbedding c q=x) := by
  have hx : x ∈ (SourceGlobalAffine318.chartEmbedding c).opensRange ⊔
      (InfinityGlobalScheme318.chartEmbedding c).opensRange := by
    rw [ContactGlobalSmooth318.actual_charts_cover]
    trivial
  rcases hx with hx|hx
  · obtain ⟨a,rfl⟩ := hx
    obtain ⟨i,q,hq⟩ := InvariantChartCover318.finite_localizations_cover
      (SourceDenominatorCover318.denominator c) (SourceDenominatorCover318.span_top c) a
    exact Or.inl ⟨i,q,congrArg (SourceGlobalAffine318.chartEmbedding c) hq⟩
  · exact Or.inr hx

@[expose] def chart : Option (Fin 4) → Scheme
  | none => ReciprocalInfinityNormalization318.neighborhood c
  | some i => Spec (CommRingCat.of (BranchRing c i))
@[expose] def embedding : (i : Option (Fin 4)) → chart c i ⟶ ContactGlobalSmooth318.Model c
  | none => InfinityGlobalScheme318.chartEmbedding c
  | some i => branchEmbedding c i
instance embedding_open (i : Option (Fin 4)) : IsOpenImmersion (embedding c i) := by
  cases i
  · exact InfinityGlobalScheme318.chartEmbedding_open c
  · exact branchEmbedding_open c _

/-- A genuine five-chart open cover trivializing the intrinsic source
cotangent sheaf everywhere, including all branch points and infinity. -/
@[expose] def cover : (ContactGlobalSmooth318.Model c).OpenCover where
  I₀ := Option (Fin 4)
  X := chart c
  f := embedding c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro x
    rcases frames_cover c x with ⟨i,q,hq⟩|⟨q,hq⟩
    · exact ⟨some i,q,hq⟩
    · exact ⟨none,q,hq⟩

@[expose] def localFrame (i : Option (Fin 4)) :
    (ContactIntrinsicDifferentials318.omega c).restrict (embedding c i) ≅
      SheafOfModules.unit (chart c i).ringCatSheaf := by
  cases i
  · exact infinityFrame c
  · exact branchFrame c _
end ContactIntrinsicFrames318
