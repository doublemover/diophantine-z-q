module
public import AffineClosedQuotientExtraction318
public import VaryingWholeIdealFamily318
public section
noncomputable section
namespace AffineWholeQuotientProjection318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
  {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of (S ⊗[R] A))) [IsClosedImmersion f]
abbrev ideal := AffineClosedQuotientExtraction318.ideal (S ⊗[R] A) f
abbrev quotient := (S ⊗[R] A) ⧸ ideal R A S f
abbrev projection := f ≫ VaryingSourceCoefficientPullback318.projection R A S
abbrev quotientProjection := VaryingWholeIdealFamily318.projection R A S (ideal R A S f)
abbrev comparison : Z ≅ Spec (CommRingCat.of (quotient R A S f)) :=
  AffineClosedQuotientExtraction318.comparison (S ⊗[R] A) f
@[reassoc] lemma comparison_projection : (comparison R A S f).hom ≫ quotientProjection R A S f=projection R A S f := by
  change (comparison R A S f).hom ≫
    AffineQuotientFactorRigidity318.into (S ⊗[R] A) (ideal R A S f) ≫
      VaryingSourceCoefficientPullback318.projection R A S=_
  rw [← Category.assoc,AffineClosedQuotientExtraction318.comparison_into]
  rfl
@[reassoc] lemma inverse_projection : (comparison R A S f).inv ≫ projection R A S f=quotientProjection R A S f := by
  rw [← comparison_projection,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
lemma spec_coefficient : Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A S f)))=quotientProjection R A S f := by
  change Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A S f)))=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal R A S f))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
  rw [← Spec.map_comp]
  rfl
end AffineWholeQuotientProjection318
