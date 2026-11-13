module
public import ContactNowhereZeroTargetNormalizationRebuild318
public import SchemeOpenRangePullbackRebuild318
public section
noncomputable section
namespace ContactNowhereZeroTargetCoverRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "j" => ContactOriginalGlobalKernelNormalizationRebuild318.original R c L
local notation "k" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "m" => ContactNowhereZeroTargetNormalizationRebuild318.map R c L
include R c L in
lemma range_inclusion : Set.range k=n ⁻¹' Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  change Set.range k=↑(n ⁻¹ᵁ V)
  rw [ContactKernelGlobalTargetPreimageRebuild318.preimage]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change j (k y) ∈ ContactArbitraryNowhereZeroOpen318.locus R c L
    rw [show j (k y)=(y:ContactArbitrarySectionParameter318.parameterScheme R c L) from
      congrArg (fun q => q y) (ContactNowhereZeroSourceOpenRebuild318.original R c L)]
    exact y.property
  · intro hx
    let y : N := ⟨j x,hx⟩
    refine ⟨y,?_⟩
    apply j.isOpenEmbedding.injective
    exact congrArg (fun q => q y) (ContactNowhereZeroSourceOpenRebuild318.original R c L)
include R c L in
/-- The original nowhere-zero normalization is EXACTLY the restriction
of the old smooth full-kernel normalization to the produced target open. -/
lemma cartesian : IsPullback k m n V.ι :=
  SchemeOpenRangePullbackRebuild318.square k m n V.ι
    (ContactNowhereZeroTargetNormalizationRebuild318.factor R c L).symm
    (range_inclusion R c L)
instance smooth : Smooth m := MorphismProperty.of_isPullback (cartesian R c L) inferInstance
/-- Genuine smooth fppf covering of the represented normalized target
open; no cover of the coefficient base or varying Picard scheme is asserted. -/
lemma fppf : Flat m ∧ Surjective m ∧ LocallyOfFinitePresentation m :=
  ⟨inferInstance,inferInstance,inferInstance⟩
end ContactNowhereZeroTargetCoverRebuild318
