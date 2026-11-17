module
public import NormalizationChartFieldPoint318
public import OriginalIntegerRationalChartFieldSquares318
public section
noncomputable section
namespace OriginalIntegerRationalGenericPoint318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
universe u

private theorem identified_chart_point {A B C F : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j) [Algebra A C] (h : B ⟶ F) :
    letI := φ.hom.toAlgebra
    ∀ e : integralClosure A B ≃ₐ[A] C,
    Spec.map (CommRingCat.ofHom
      (h.hom.comp ((integralClosure A B).val.toRingHom.comp e.symm.toRingHom))) ≫
      (Spec.map (CommRingCat.ofHom
        ((InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).trans
          e.toRingEquiv).toRingHom) ≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage
          f.fromNormalization).fromSpec) = Spec.map h ≫ f.toNormalization := by
  letI := φ.hom.toAlgebra
  intro e
  have hs := NormalizationSourceCompatibility318.factored_chart_original φ j f hf e
  rw [← hs, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem spec_equiv_field {R C F : Type u} [CommRing R] [CommRing C] [CommRing F]
    (e : R ≃+* C) (h : C →+* F) :
    Spec.map (CommRingCat.ofHom (h.comp e.toRingHom)) ≫
      (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).hom =
    Spec.map (CommRingCat.ofHom h) := by
  change Spec.map (CommRingCat.ofHom (h.comp e.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  ext z
  exact congrArg h (e.apply_symm_apply z)

variable (c : Fin 4 → ℚˣ)
open OriginalIntegerRationalOverlapSquares318
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The ONE specified point of the original normalization coming from the
original open-order embedding into its original function field. -/
@[expose] def canonicalPoint : Spec (CommRingCat.of (L c)) ⟶
    (ContactProjectiveModel318.coverMap c).normalization :=
  Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.openEmbedding c)) ≫
    (ContactProjectiveModel318.coverMap c).toNormalization

/-- The whole finite original chart carries this exact canonical point. -/
theorem finite_original_point :
    Spec.map (CommRingCat.ofHom (ContactKummerOrder318.embedding c)) ≫
      SourceGlobalAffine318.chartEmbedding c = canonicalPoint c := by
  letI : Algebra ContactKummerOrder318.R (ContactKummerOrder318.OpenOrder c) :=
    (ContactGlobalProper318.finitePolynomial c).toAlgebra
  let e := SourceClosureComparison318.sourceClosureEquiv c
    (SourceGlobalAffine318.source_integrallyClosed c)
  have he : (SourceOpenFractionField318.openEmbedding c).comp
      ((integralClosure ContactKummerOrder318.R (ContactKummerOrder318.OpenOrder c)).val.toRingHom.comp
        e.symm.toRingHom) = ContactKummerOrder318.embedding c := by
    ext z
    have hz := SourceClosureComparison318.sourceClosureEquiv_embedding c
      (SourceGlobalAffine318.source_integrallyClosed c) (e.symm z)
    simpa only [AlgEquiv.apply_symm_apply] using hz.symm
  have hs := identified_chart_point
    (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c))
    (JLineAtlas318.chart ℚ 1) (ContactProjectiveModel318.coverMap c)
    (ContactGlobalProper318.finite_factor c)
    (CommRingCat.ofHom (SourceOpenFractionField318.openEmbedding c)) e
  rw [he] at hs
  exact hs

/-- The whole reciprocal original section chart carries that SAME point. -/
theorem reciprocal_original_point :
    Spec.map (CommRingCat.ofHom
      (OriginalIntegerRationalChartFieldSquares318.reciprocalSectionsField c)) ≫
      (OriginalIntegerRationalReciprocalChart318.actualOpen c).2.fromSpec =
    canonicalPoint c := by
  have hs := NormalizationChartFieldPoint318.canonical_chart_point
    (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap
      (ContactKummerOrder318.OpenOrder c)))
    (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.coverMap c)
    (ContactGlobalProper318.reciprocal_factor c)
    (CommRingCat.ofHom (SourceOpenFractionField318.openEmbedding c))
  rw [← Category.assoc, ← Spec.map_comp] at hs
  exact hs

/-- The finite rational tensor-chart map agrees at the actual generic point,
not only on its coefficient ring or on an abstract field isomorphism. -/
theorem finite_tensor_point :
    Spec.map (CommRingCat.ofHom (finiteEmbedding c)) ≫
      OriginalIntegerRationalSourceIdentification318.rationalFiberChart c =
    canonicalPoint c := by
  rw [← OriginalIntegerRationalChartFieldSquares318.finite_chart_field_square]
  change Spec.map _ ≫ ((Scheme.Spec.mapIso
    (OriginalIntegerRationalSourceIdentification318.integerRationalFiberOrderEquiv c).symm.toCommRingCatIso.op).hom ≫
      SourceGlobalAffine318.chartEmbedding c) = _
  rw [← Category.assoc, spec_equiv_field, finite_original_point]

/-- The reciprocal rational tensor-chart map agrees at that SAME point. -/
theorem reciprocal_tensor_point :
    Spec.map (CommRingCat.ofHom (infinityEmbedding c)) ≫
      OriginalIntegerRationalReciprocalChart318.fiberChart c = canonicalPoint c := by
  rw [← OriginalIntegerRationalChartFieldSquares318.reciprocal_chart_field_square]
  change Spec.map _ ≫ ((Scheme.Spec.mapIso
    (OriginalIntegerRationalReciprocalChart318.fiberSectionsEquiv c).symm.toCommRingCatIso.op).hom ≫
      (OriginalIntegerRationalReciprocalChart318.actualOpen c).2.fromSpec) = _
  rw [← Category.assoc, spec_equiv_field, reciprocal_original_point]

end OriginalIntegerRationalGenericPoint318
