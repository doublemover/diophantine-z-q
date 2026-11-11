module
public import ContactOriginalFiniteRingSpan318
public import AffineSpecOriginalRingTransport318
public section
noncomputable section
namespace ContactOriginalInfinityRingSpan318
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ContactOriginalRelativeOverlap318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
local instance : Algebra (Polynomial ℚ) (LaurentPolynomial ℚ) :=
  OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra

/-- Both ORIGINAL full tensor overlap spectra are compared via their
unchanged maps to the same original geometric intersection. -/
def comparison : Spec (oldRing c) ≅
    Spec (CommRingCat.of (ContactOverlapTensorCharts318.infinityRing c)) :=
  (ContactOverlapTensorCharts318.finiteIso c).symm ≪≫
    ContactOverlapTensorCharts318.infinityIso c

abbrev transport := AffineSpecOriginalRingTransport318.hom (comparison c)

lemma base_square : (transport c).comp
    (algebraMap (LaurentPolynomial ℚ) (ContactOverlapTensorCharts318.infinityRing c)) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) := by
  have h : CommRingCat.ofHom
      (algebraMap (LaurentPolynomial ℚ) (ContactOverlapTensorCharts318.infinityRing c)) ≫
      Spec.preimage (comparison c).hom =
        CommRingCat.ofHom (algebraMap (LaurentPolynomial ℚ) (oldRing c)) := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_preimage]
    rw [← ContactOverlapTensorCharts318.infinityIso_inv_base]
    simp only [comparison,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.hom_inv_id_assoc]
    exact ContactOverlapTensorCharts318.finiteIso_inv_base c
  exact congrArg CommRingCat.Hom.hom h

lemma chart_square : (transport c).comp
    (Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
      (A := LaurentPolynomial ℚ) (B := ContactWholeInfinityAlgebra318.Ring c)).toRingHom =
      (infinityMap c).toRingHom := by
  have h : CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
        (A := LaurentPolynomial ℚ) (B := ContactWholeInfinityAlgebra318.Ring c)).toRingHom ≫
      Spec.preimage (comparison c).hom = CommRingCat.ofHom (infinityMap c).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_preimage,rationalMap_spec]
    rw [← ContactOverlapTensorCharts318.infinityIso_inv_chart]
    simp only [comparison,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.hom_inv_id_assoc]
    rfl
  exact congrArg CommRingCat.Hom.hom h

lemma transport_tmul (l : LaurentPolynomial ℚ) (b : ContactWholeInfinityAlgebra318.Ring c) :
    transport c (l ⊗ₜ[Polynomial ℚ] b) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) l * infinityMap c b := by
  have ht : l ⊗ₜ[Polynomial ℚ] b =
      algebraMap (LaurentPolynomial ℚ) (ContactOverlapTensorCharts318.infinityRing c) l *
        Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
          (A := LaurentPolynomial ℚ) (B := ContactWholeInfinityAlgebra318.Ring c) b := by
    simp
  rw [ht,map_mul]
  rw [RingHom.congr_fun (base_square c) l, RingHom.congr_fun (chart_square c) b]

/-- The reciprocal chart spans the SAME old Laurent overlap as the finite
chart. The proof uses the full actual tensor comparison and both of its
projection equations, not a second unrelated section module. -/
lemma old_span : Submodule.span (LaurentPolynomial ℚ) (Set.range (infinityMap c)) = ⊤ := by
  let P := Submodule.span (LaurentPolynomial ℚ) (Set.range (infinityMap c))
  apply top_unique
  intro x _
  obtain ⟨z,rfl⟩ := AffineSpecOriginalRingTransport318.surjective (comparison c) x
  change transport c z ∈ P
  induction z using TensorProduct.inductionOn with
  | tmul l b =>
      rw [transport_tmul]
      change l • infinityMap c b ∈ P
      exact P.smul_mem l (Submodule.subset_span ⟨b,rfl⟩)
  | add x y hx hy => simpa only [map_add] using P.add_mem hx hy

variable (R : CommRingCat.{0}) [Algebra ℚ R]
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- Every coefficient test retains the actual reciprocal-chart spanning
statement on the ONE original overlap, with no reducedness assumption. -/
theorem span : Submodule.span (LaurentPolynomial R)
    (Set.range (RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
      (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c)).hom) = ⊤ :=
  RelativeLaurentRingSpan318.basechange_span (CommRingCat.of ℚ) R
    (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c) (old_span c)
end ContactOriginalInfinityRingSpan318
