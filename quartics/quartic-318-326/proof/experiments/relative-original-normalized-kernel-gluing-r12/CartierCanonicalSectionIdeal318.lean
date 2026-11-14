module
public import CartierFramedAffineCover318
public import FramedAffineZeroKernel318
public section
noncomputable section
namespace CartierCanonicalSectionIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CartierCanonicalSection318 AffineQuotientKernelSections318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (hp : OriginalRegularClosedCharts318.Property p)
  (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j]
  (i : (idealLine p hp).Index) (hi : j ''ᵁ ⊤≤(idealLine p hp).opens i)
local notation "D" => divisorLine p hp
local notation "s" => section p hp
include hi in
/-- The canonical inverse-ideal section cuts out the EXACT extracted
closed quotient in its original affine chart, including nilpotents. -/
lemma ideal : SectionZeroAffineRefinement318.sectionIdeal A j D s=
    AffineClosedRestriction318.ideal p A j := by
  have he := FramedAffineZeroKernel318.coordinate_ideal A j D s
    (LineArrowInverseLocal318.inverseFrame (idealLine p hp) i (j ''ᵁ ⊤) hi).symm
  have hc := coordinate p hp i (j ''ᵁ ⊤) hi
  rw [hc] at he
  have hk := CartierCanonicalSection318.ideal p hp i (chartOpen A j) hi
  have hm := he.trans hk
  have hb := congrArg (Ideal.comap (coefficient A j).hom) hm
  rw [Ideal.comap_map_of_bijective _ (AffineZeroKernelRestriction318.coefficient_bijective A j)] at hb
  exact hb.trans (AffineClosedRestrictionChart318.kernel p A j)
end CartierCanonicalSectionIdeal318
