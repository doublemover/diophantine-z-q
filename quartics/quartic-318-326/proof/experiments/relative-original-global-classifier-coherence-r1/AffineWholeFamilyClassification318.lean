module
public import AffineFiniteProjectiveQuotient318
public import VaryingProjectiveQuotientFamily318
public section
noncomputable section
namespace AffineWholeFamilyClassification318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineWholeQuotientProjection318
open scoped TensorProduct
universe u
variable (R A S ι : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] {Z : Scheme.{u}}
  (f : Z ⟶ Spec (CommRingCat.of (S ⊗[R] A))) [IsClosedImmersion f]
  [IsFinite (projection R A S f)] [Flat (projection R A S f)]
  [LocallyOfFinitePresentation (projection R A S f)]
  (h : ∀ x : PrimeSpectrum S,(projection R A S f).finrank x=Fintype.card ι)
local notation "I" => AffineFiniteProjectiveQuotient318.data R A S f ι h
@[expose] def point : VaryingParameterPoint318.Point R A ι S :=
  VaryingProjectiveQuotientEquiv318.equivalence R A ι S I
/-- Classification recovers the SAME entire original closed family,
not just an isomorphic abstract finite module or a chosen frame. -/
@[expose] def familyComparison : Z ≅ VaryingParameterPointFamily318.family R A ι S (point R A S ι f h) :=
  comparison R A S f ≪≫ VaryingProjectiveQuotientFamily318.comparison R A ι S I
@[reassoc] lemma comparison_into : (familyComparison R A S ι f h).hom ≫
    VaryingParameterPointFamily318.intoSource R A ι S (point R A S ι f h)=f := by
  rw [familyComparison,Iso.trans_hom,Category.assoc,VaryingProjectiveQuotientFamily318.comparison_into]
  exact AffineClosedQuotientExtraction318.comparison_into (S ⊗[R] A) f
@[reassoc] lemma comparison_projection : (familyComparison R A S ι f h).hom ≫
    VaryingParameterPointFamily318.projection R A ι S (point R A S ι f h)=projection R A S f := by
  rw [← VaryingParameterPointFamily318.into_projection,← Category.assoc,comparison_into]
  rfl
lemma recovered_ideal : VaryingParameterPointIdeal318.ideal R A ι S (point R A S ι f h)=ideal R A S f :=
  VaryingProjectiveQuotientEquiv318.recovered_ideal R A ι S I
end AffineWholeFamilyClassification318
