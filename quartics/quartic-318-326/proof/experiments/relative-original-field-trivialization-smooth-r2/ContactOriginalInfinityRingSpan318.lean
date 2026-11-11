module
public import ContactOriginalFiniteRingSpan318
public import AffineSpecOriginalRingTransport318
public section
noncomputable section
namespace ContactOriginalInfinityRingSpan318
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ContactOriginalRelativeOverlap318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section PackedTensor
variable (P A B : CommRingCat.{0}) (f : P →+* A) [Algebra P B]
/-- The original reciprocal pure tensor with its scalar action packaged
at abstract rings, before specializing Laurent polynomial instances. -/
@[expose] def tensorTmul (a : A) (b : B) : ContactOverlapTensorCharts318.tensorRing P A B f := by
  letI := f.toAlgebra
  exact a ⊗ₜ[P] b
lemma tensor_tmul (a : A) (b : B) : tensorTmul P A B f a b=
    algebraMap A (ContactOverlapTensorCharts318.tensorRing P A B f) a *
      ContactOverlapTensorCharts318.tensorRight P A B f b := by
  letI := f.toAlgebra
  change a ⊗ₜ[P] b=(a ⊗ₜ[P] (1:B))*((1:A) ⊗ₜ[P] b)
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
lemma tensor_span : Submodule.span A (Set.range (ContactOverlapTensorCharts318.tensorRight P A B f))=⊤ := by
  letI := f.toAlgebra
  change Submodule.span A (Set.range (Algebra.TensorProduct.includeRight (R:=P) (A:=A) (B:=B)).toRingHom)=⊤
  let V := Submodule.span A (Set.range (Algebra.TensorProduct.includeRight (R:=P) (A:=A) (B:=B)).toRingHom)
  have h : ∀ z : A ⊗[P] B,z∈V := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      have hb : (1:A) ⊗ₜ[P] b∈V := Submodule.subset_span ⟨b,rfl⟩
      have ht : a ⊗ₜ[P] b=a • ((1:A) ⊗ₜ[P] b) := by
        rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
      rw [ht]
      exact V.smul_mem a hb
    | add x y hx hy => exact V.add_mem hx hy
  apply top_unique
  intro z _
  exact h z
end PackedTensor
variable (c : Fin 4 → ℚˣ)

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
  change (AffineSpecOriginalRingTransport318.hom (comparison c)).comp _=_
  rw [AffineSpecOriginalRingTransport318.hom_eq]
  exact congrArg CommRingCat.Hom.hom h

lemma chart_square : (transport c).comp (ContactOverlapTensorCharts318.infinityRight c)=
    (infinityMap c).toRingHom := by
  have h : CommRingCat.ofHom (ContactOverlapTensorCharts318.infinityRight c) ≫
      Spec.preimage (comparison c).hom=CommRingCat.ofHom (infinityMap c).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_preimage,rationalMap_spec]
    rw [← ContactOverlapTensorCharts318.infinityIso_inv_chart]
    simp only [comparison,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc]
  change (AffineSpecOriginalRingTransport318.hom (comparison c)).comp _=_
  rw [AffineSpecOriginalRingTransport318.hom_eq]
  exact congrArg CommRingCat.Hom.hom h

lemma base_apply (l : LaurentPolynomial ℚ) :
    transport c (algebraMap (LaurentPolynomial ℚ) (ContactOverlapTensorCharts318.infinityRing c) l)=
      ((algebraMap (LaurentPolynomial ℚ) (oldRing c)) : LaurentPolynomial ℚ →+* oldRing c) l := by
  have h := RingHom.congr_fun (base_square c) l
  exact h

lemma chart_apply (b : ContactWholeInfinityAlgebra318.Ring c) :
    transport c (ContactOverlapTensorCharts318.infinityRight c b)=infinityMap c b := by
  have h := RingHom.congr_fun (chart_square c) b
  exact h

lemma transport_tmul (l : LaurentPolynomial ℚ) (b : ContactWholeInfinityAlgebra318.Ring c) :
    transport c (tensorTmul (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of (LaurentPolynomial ℚ))
      (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) OriginalLaurentProjectiveOverlap318.infinityHom l b)=
      ((algebraMap (LaurentPolynomial ℚ) (oldRing c)) : LaurentPolynomial ℚ →+* oldRing c) l * infinityMap c b := by
  have ht := tensor_tmul (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of (LaurentPolynomial ℚ))
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
    OriginalLaurentProjectiveOverlap318.infinityHom l b
  rw [ht,map_mul,base_apply,chart_apply]

/-- The reciprocal chart spans the SAME old Laurent overlap as the finite
chart. The proof uses the full actual tensor comparison and both of its
projection equations, not a second unrelated section module. -/
lemma old_span : Submodule.span (LaurentPolynomial ℚ) (Set.range (infinityMap c)) = ⊤ := by
  let P := Submodule.span (LaurentPolynomial ℚ) (Set.range (infinityMap c))
  apply top_unique
  intro x _
  obtain ⟨z,rfl⟩ := AffineSpecOriginalRingTransport318.surjective (comparison c) x
  change transport c z ∈ P
  have hz : z∈Submodule.span (LaurentPolynomial ℚ) (Set.range (ContactOverlapTensorCharts318.infinityRight c)) := by
    have hs : Submodule.span (LaurentPolynomial ℚ)
        (Set.range (ContactOverlapTensorCharts318.infinityRight c))=⊤ :=
      tensor_span (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of (LaurentPolynomial ℚ))
        (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
        OriginalLaurentProjectiveOverlap318.infinityHom
    rw [hs]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨b,rfl⟩
    rw [chart_apply]
    exact Submodule.subset_span ⟨b,rfl⟩
  · simpa only [map_zero] using P.zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using P.add_mem hx hy
  · intro l x _ hx
    have he : transport c (l • x)=l • transport c x := by
      simp only [Algebra.smul_def,map_mul]
      rw [base_apply]
    rw [he]
    exact P.smul_mem l hx

variable (R : CommRingCat.{0}) [Algebra ℚ R]
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=LaurentPolynomial ℚ) (A:=oldRing c)
    (RingHom.ext_rat _ _)

/-- Every coefficient test retains the actual reciprocal-chart spanning
statement on the ONE original overlap, with no reducedness assumption. -/
theorem span : Submodule.span (LaurentPolynomial R)
    (Set.range (RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
      (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c)).hom) = ⊤ :=
  RelativeLaurentRingSpan318.basechange_span (CommRingCat.of ℚ) R
    (ContactOriginalRelativePolynomialCharts318.infinityRing c) (oldRing c) (infinityMap c) (old_span c)
end ContactOriginalInfinityRingSpan318
