module
public import PrimeThreeActualLocalUniversal318
public import OriginalPrimeThreeNativeChartCover318
public section
noncomputable section
namespace PrimeThreeActualTestCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PrimeThreeGluedSecondModification318 PrimeThreeGluedFirstUPreimage318
open PrimeThreeSecondFirstOverlapBridges318 PrimeThreeSelectedFirstUResidualCenter318
open OriginalPrimeThreeFirstUNativeChart318 PrimeThreeActualLocalUniversal318

@[expose] def baseRing : Fin 3 → CommRingCat :=
  ![CommRingCat.of LocalU, CommRingCat.of (FirstOther 0), CommRingCat.of (FirstOther 1)]

@[expose] def baseInclusion : ∀ i, Spec (baseRing i) ⟶
    OriginalPrimeThreeNativeReesProj318.actualReesProj
  | 0 => explicitFirstUInclusion
  | 1 => OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 1
  | 2 => OriginalPrimeThreeNativeReesProj318.nativeChartInclusion 2

instance baseInclusion_openImmersion (i : Fin 3) : IsOpenImmersion (baseInclusion i) := by
  fin_cases i <;> dsimp only [baseInclusion] <;> infer_instance

theorem baseInclusion_range (i : Fin 3) : (baseInclusion i).opensRange =
    Proj.basicOpen OriginalPrimeThreeNativeReesProj318.grading
      (OriginalPrimeThreeNativeReesProj318.generator i) := by
  fin_cases i
  · exact firstU_range
  · exact Proj.opensRange_awayι _ _ _ _
  · exact Proj.opensRange_awayι _ _ _ _

theorem base_charts_cover (x : OriginalPrimeThreeNativeReesProj318.actualReesProj) :
    ∃ i y, baseInclusion i y = x := by
  obtain ⟨i, hi⟩ := OriginalPrimeThreeNativeChartCover318.exists_native_chart x
  rw [← baseInclusion_range i] at hi
  exact ⟨i, hi⟩

/-- The actual first-U/V/W cover of the selected PointRing first Rees Proj. -/
@[expose] def baseCover : OriginalPrimeThreeNativeReesProj318.actualReesProj.AffineOpenCover where
  I₀ := Fin 3
  X := baseRing
  f := baseInclusion
  idx x := (base_charts_cover x).choose
  covers x := (base_charts_cover x).choose_spec

variable {X : Scheme} (f : X ⟶ OriginalPrimeThreeNativeReesProj318.actualReesProj)

/-- The native pullback cover of an arbitrary test scheme. -/
@[expose] def testCover : X.OpenCover := baseCover.openCover.pullback₁ f

@[expose] def testBase (i : Fin 3) : (testCover f).X i ⟶ Spec (baseRing i) :=
  baseCover.openCover.pullbackHom f i

@[reassoc] theorem testBase_inclusion (i : Fin 3) :
    testBase f i ≫ baseInclusion i = (testCover f).f i ≫ f :=
  baseCover.openCover.pullbackHom_map f i

/-- A candidate piecewise lift is required only to lie over the actual
base map. Cross-chart compatibility will be proved, not assumed. -/
variable (k : ∀ i, (testCover f).X i ⟶ gluedSecondModification)
variable (hk : ∀ i, k i ≫ toFirstBlowup = (testCover f).f i ≫ f)

theorem pair_base_agreement (i j : Fin 3) :
    (pullback.fst ((testCover f).f i) ((testCover f).f j) ≫ k i) ≫ toFirstBlowup =
      (pullback.snd ((testCover f).f i) ((testCover f).f j) ≫ k j) ≫ toFirstBlowup := by
  simp only [Category.assoc, hk]
  simpa only [Category.assoc] using
    congrArg (fun m => m ≫ f) (pullback.condition ((testCover f).f i) ((testCover f).f j))

/-- If the right chart is unchanged, its actual canonical pullback is an
isomorphism. Thus two global lifts over this intersection agree, without
canceling the whole modification or introducing an ideal premise. -/
theorem pair_agreement_right_other (i : Fin 3) (j : Fin 2) :
    pullback.fst ((testCover f).f i) ((testCover f).f j.succ) ≫ k i =
      pullback.snd ((testCover f).f i) ((testCover f).f j.succ) ≫ k j.succ := by
  let b := pullback.snd ((testCover f).f i) ((testCover f).f j.succ)
  let h := b ≫ testBase f j.succ
  have hu : ∃! z : pullback ((testCover f).f i) ((testCover f).f j.succ) ⟶
      gluedSecondModification, z ≫ toFirstBlowup = h ≫ baseInclusion j.succ := by
    fin_cases j
    · exact existsUnique_over_other 0 h
    · exact existsUnique_over_other 1 h
  have hr : (b ≫ k j.succ) ≫ toFirstBlowup = h ≫ baseInclusion j.succ := by
    rw [Category.assoc, hk, h, Category.assoc, testBase_inclusion]
  exact hu.unique ((pair_base_agreement f k hk i j.succ).trans hr) hr

/-- Every pair compatibility condition for the genuine test cover follows
from the identity over V/W and the monomorphism of each test-cover open. -/
theorem pair_agreement (i j : Fin 3) :
    pullback.fst ((testCover f).f i) ((testCover f).f j) ≫ k i =
      pullback.snd ((testCover f).f i) ((testCover f).f j) ≫ k j := by
  have hdiag (i : Fin 3) :
      pullback.fst ((testCover f).f i) ((testCover f).f i) =
        pullback.snd ((testCover f).f i) ((testCover f).f i) :=
    (cancel_mono ((testCover f).f i)).mp pullback.condition
  have hleft (a : Fin 2) (b : Fin 3) :
      pullback.fst ((testCover f).f a.succ) ((testCover f).f b) ≫ k a.succ =
        pullback.snd ((testCover f).f a.succ) ((testCover f).f b) ≫ k b := by
    apply (cancel_epi ((pullbackSymmetry ((testCover f).f b) ((testCover f).f a.succ)).hom)).mp
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (pair_agreement_right_other f k hk b a).symm
  fin_cases j
  · fin_cases i
    · rw [hdiag]
    · exact hleft 0 0
    · exact hleft 1 0
  · exact pair_agreement_right_other f k hk i 0
  · exact pair_agreement_right_other f k hk i 1

end PrimeThreeActualTestCover318
