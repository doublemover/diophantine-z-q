module
public import ContactNowhereZeroTargetTestsRebuild318
public section
noncomputable section
namespace ContactNowhereZeroTargetBaseChangeRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "k" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "m" => ContactNowhereZeroTargetNormalizationRebuild318.map R c L
variable (T : Scheme.{0}) (t : T ⟶ V.toScheme)
/-- The actual fppf cover of an arbitrary target test, constructed by
base change, not supplied as an effectivity or local-lifting assumption. -/
abbrev source : Scheme := pullback t m
abbrev projection : source R c L T t ⟶ T := pullback.fst t m
abbrev section : source R c L T t ⟶ N := pullback.snd t m
@[reassoc] lemma normalized : section R c L T t ≫ m=projection R c L T t ≫ t :=
  (pullback.condition (f := t) (g := m)).symm
instance smooth : Smooth (projection R c L T t) := inferInstance
instance surjective : Surjective (projection R c L T t) := inferInstance
lemma fppf : Flat (projection R c L T t) ∧ Surjective (projection R c L T t) ∧
    LocallyOfFinitePresentation (projection R c L T t) := ⟨inferInstance,inferInstance,inferInstance⟩
/-- Its local lift is the original nowhere-zero section family and
recovers the SAME full-kernel normalization after the actual open inclusion. -/
@[reassoc] lemma original_normalized : section R c L T t ≫ k ≫ n=
    projection R c L T t ≫ t ≫ V.ι := by
  rw [(ContactNowhereZeroTargetCoverRebuild318.cartesian R c L).w,
    ←Category.assoc,normalized,Category.assoc]
end ContactNowhereZeroTargetBaseChangeRebuild318
