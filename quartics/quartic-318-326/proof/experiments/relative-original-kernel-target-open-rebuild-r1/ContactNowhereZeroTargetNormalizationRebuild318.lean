module
public import ContactKernelGlobalTargetPreimageRebuild318
public section
noncomputable section
namespace ContactNowhereZeroTargetNormalizationRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "S" => ContactOriginalGlobalKernelNormalizationRebuild318.source R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "j" => ContactOriginalGlobalKernelNormalizationRebuild318.original R c L
local notation "k" => ContactNowhereZeroSourceOpenRebuild318.inclusion R c L
local notation "m" => ContactNowhereZeroNormalizationRebuild318.map R c L
include R c L in
lemma range_subset : Set.range m ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x,rfl⟩
  change k x ∈ n ⁻¹ᵁ V
  rw [ContactKernelGlobalTargetPreimageRebuild318.preimage]
  change j (k x) ∈ ContactArbitraryNowhereZeroOpen318.locus R c L
  have hk := congrArg (fun q => q x) (ContactNowhereZeroSourceOpenRebuild318.original R c L)
  rw [hk]
  exact x.property
/-- The SAME original nowhere-zero family now maps into the produced
GLOBAL target open. No replacement of its line parameter has occurred. -/
def map : N ⟶ ContactKernelGlobalTargetOpenRebuild318.scheme R c L :=
  IsOpenImmersion.lift V.ι m (range_subset R c L)
@[reassoc] lemma factor : map R c L ≫ V.ι=m := IsOpenImmersion.lift_fac _ _ _
lemma unique (g : N ⟶ ContactKernelGlobalTargetOpenRebuild318.scheme R c L)
    (hg : g ≫ V.ι=m) : g=map R c L :=
  (cancel_mono V.ι).mp (hg.trans (factor R c L).symm)
/-- Surjectivity is proved from the actual global normalization and the
EXACT descended-open preimage. It is onto the target open, NOT the base. -/
instance surjective : Surjective (map R c L) := by
  constructor
  intro z
  obtain ⟨x,hx⟩ := (inferInstance : Surjective n).surj (z:ContactOriginalNormalizedKernelScheme318.scheme R c L)
  have hxV : x ∈ n ⁻¹ᵁ V := by change n x ∈ V;rw [hx];exact z.property
  rw [ContactKernelGlobalTargetPreimageRebuild318.preimage] at hxV
  let y : N := ⟨j x,hxV⟩
  have hky : k y=x := by
    apply j.isOpenEmbedding.injective
    exact congrArg (fun q => q y) (ContactNowhereZeroSourceOpenRebuild318.original R c L)
  refine ⟨y,?_⟩
  apply Subtype.ext
  change ((map R c L y):ContactOriginalNormalizedKernelScheme318.scheme R c L)=(z:ContactOriginalNormalizedKernelScheme318.scheme R c L)
  calc
    ((map R c L y):ContactOriginalNormalizedKernelScheme318.scheme R c L)=n (k y) :=
      congrArg (fun q => q y) (factor R c L)
    _=(z:ContactOriginalNormalizedKernelScheme318.scheme R c L) := by rw [hky,hx]
@[reassoc] lemma coefficient : map R c L ≫ V.ι ≫
    ContactOriginalNormalizedKernelScheme318.projection R c L =
    ContactArbitraryNowhereZeroOpen318.into R c L ≫ parameterProjection R c L := by
  rw [←Category.assoc,factor,ContactNowhereZeroNormalizationRebuild318.coefficient]
end ContactNowhereZeroTargetNormalizationRebuild318
