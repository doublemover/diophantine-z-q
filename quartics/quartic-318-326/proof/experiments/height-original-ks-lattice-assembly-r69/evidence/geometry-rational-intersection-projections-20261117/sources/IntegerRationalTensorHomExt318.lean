module
public import IntegerChartBaseChangeIso318
public section
noncomputable section
namespace IntegerRationalTensorHomExt318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
variable {A : Type} [CommRing A] {W : Scheme}

/-- The original-ring and rational-coefficient projections jointly detect
maps into the actual tensor affine scheme. -/
theorem hom_ext (f g : W ⟶ Spec (CommRingCat.of (A ⊗[ℤ] ℚ)))
    (hA : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[ℤ] ℚ))) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[ℤ] ℚ))))
    (hQ : f ≫ Spec.map (CommRingCat.ofHom
        (IntegerRationalTensorNaturality318.rationalCoefficient A)) =
      g ≫ Spec.map (CommRingCat.ofHom
        (IntegerRationalTensorNaturality318.rationalCoefficient A))) : f = g := by
  apply (cancel_mono (pullbackSpecIso ℤ A ℚ).inv).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackSpecIso_inv_fst'] using hA
  · simpa only [Category.assoc, pullbackSpecIso_inv_snd,
      IntegerRationalTensorNaturality318.rationalCoefficient] using hQ

end IntegerRationalTensorHomExt318
