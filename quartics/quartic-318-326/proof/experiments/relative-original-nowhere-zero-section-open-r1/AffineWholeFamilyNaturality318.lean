module
public import AffineWholeFamilyClassification318
public import AffineClosedIdealBaseChange318
public section
noncomputable section
namespace AffineWholeFamilyNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineWholeQuotientProjection318 AffineWholeFamilyClassification318
open scoped TensorProduct
universe u
variable (R A S T ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Fintype ι] [DecidableEq ι]
  (φ : S →ₐ[R] T) {Z W : Scheme.{u}}
  (f : Z ⟶ Spec (CommRingCat.of (S ⊗[R] A))) (g : W ⟶ Spec (CommRingCat.of (T ⊗[R] A)))
  [IsClosedImmersion f] [IsClosedImmersion g]
  [IsFinite (projection R A S f)] [Flat (projection R A S f)] [LocallyOfFinitePresentation (projection R A S f)]
  [IsFinite (projection R A T g)] [Flat (projection R A T g)] [LocallyOfFinitePresentation (projection R A T g)]
  (hf : ∀ x,(projection R A S f).finrank x=Fintype.card ι)
  (hg : ∀ x,(projection R A T g).finrank x=Fintype.card ι)
  (k : W ⟶ Z)
  (H : IsPullback k g f (VaryingSourceCoefficientPullback318.sourceChange R A S T φ))
/-- Actual Cartesian family base change gives the literal ideal map and
therefore the exact same natural classifying point. -/
lemma natural : point R A T ι g hg=VaryingParameterPoint318.map R A ι S T φ (point R A S ι f hf) := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι T
  rw [recovered_ideal,VaryingPointIdealNaturality318.ideal_map,recovered_ideal]
  exact AffineClosedIdealBaseChange318.ideal_map (S ⊗[R] A) (T ⊗[R] A)
    (VaryingNormalizedIdealBaseChange318.sourceMap R A S T φ).toRingHom f g k H
end AffineWholeFamilyNaturality318
