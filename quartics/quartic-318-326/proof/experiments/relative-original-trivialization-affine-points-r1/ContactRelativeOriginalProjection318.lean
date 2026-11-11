module
public import ContactRelativeTwistCoefficientIso318
public import OriginalIsoChartScalar318
public section
noncomputable section
namespace ContactRelativeOriginalProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactRelativeWholeOpenSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

abbrev projection : curve R c ⟶ ContactProjectiveModel318.model c :=
  pullback.fst (ContactOriginalAffineTestCover318.p c) (baseMap R)

lemma finite_preimage : projection R c ⁻¹ᵁ ContactOriginalWholeRestriction318.finiteOpen c =
    finiteOpen R c := by
  simp only [finiteOpen,Scheme.Hom.image_top_eq_opensRange,finite_range]
  rfl
lemma infinity_preimage : projection R c ⁻¹ᵁ ContactOriginalWholeRestriction318.infinityOpen c =
    infinityOpen R c := by
  simp only [infinityOpen,Scheme.Hom.image_top_eq_opensRange,infinity_range]
  rfl
lemma overlap_preimage : projection R c ⁻¹ᵁ
    (ContactOriginalWholeRestriction318.finiteOpen c ⊓ ContactOriginalWholeRestriction318.infinityOpen c) =
      finiteOpen R c ⊓ infinityOpen R c := by
  rw [Scheme.Hom.preimage_inf,finite_preimage,infinity_preimage]

lemma old_image : oldInto c ''ᵁ ⊤ =
    ContactOriginalWholeRestriction318.finiteOpen c ⊓ ContactOriginalWholeRestriction318.infinityOpen c := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  rw [show (oldInto c).opensRange = (ContactOriginalLaurentOverlap318.into c).opensRange from
    Scheme.Hom.opensRange_comp_of_isIso _ _]
  exact (Scheme.Hom.image_top_eq_opensRange _).symm.trans
    (ContactOriginalWholeRestriction318.overlap_image c)

/-- The old original Laurent function and the whole tensor-spectrum
coordinate are the SAME ambient regular function. -/
lemma old_scalar (a : LaurentPolynomial ℚ) :
    ContactOriginalTwistingLine318.scalar c a =
      OriginalFunctionTransport318.chartScalar (oldInto c) _ (old_image c)
        (algebraMap (LaurentPolynomial ℚ) (oldRing c) a) :=
  OriginalIsoChartScalar318.scalar (ContactOverlapTensorCharts318.finiteIso c)
    (ContactOriginalLaurentOverlap318.into c) (ContactOriginalLaurentOverlap318.projection c)
    (CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c)))
    (ContactOverlapTensorCharts318.finiteIso_inv_base c) _
    (ContactOriginalWholeRestriction318.overlap_image c) (old_image c) a

local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The fixed ORIGINAL rational twist pulls to the actual relative
Laurent transition on every coefficient test, including negative exponents. -/
lemma monomial (d : ℤ) :
    OriginalFunctionTransport318.pullTo (projection R c) _ _ (overlap_preimage R c)
      (ContactOriginalTwistingLine318.scalar c (LaurentPolynomial.T d)) =
        ContactRelativeGeometricTwist318.scalar R c (LaurentPolynomial.T d) := by
  rw [old_scalar]
  rw [OriginalFunctionTransport318.chart_square
    (RelativeOriginalAffineChartMap318.originalB (CommRingCat.of ℚ) R (oldRing c))
    (projection R c) (into R c) (oldInto c)
    (RelativeOriginalAffineChart318.over_original _ _ _ _ _ _) _ _
    (old_image c) (overlap_image R c) (overlap_preimage R c)]
  change OriginalFunctionTransport318.chartScalar (into R c) _ (overlap_image R c)
    ((1 : R) ⊗ₜ[ℚ] algebraMap (LaurentPolynomial ℚ) (oldRing c) (LaurentPolynomial.T d)) = _
  rw [← RelativeOriginalLaurentAlgebra318.laurentMap_T ℚ R (oldRing c) d]
  rfl

lemma transition (d : ℤ) :
    Units.map (OriginalFunctionTransport318.pullTo (projection R c) _ _
      (overlap_preimage R c)).toMonoidHom (ContactOriginalTwistingLine318.transitionUnit c d) =
        ContactRelativeGeometricTwist318.transition R c d := by
  apply Units.ext
  exact monomial R c d
end ContactRelativeOriginalProjection318
