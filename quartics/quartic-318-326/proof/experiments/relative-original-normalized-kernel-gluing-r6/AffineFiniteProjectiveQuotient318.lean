module
public import AffineWholeQuotientProjection318
public import VaryingProjectiveQuotientEquiv318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public section
noncomputable section
namespace AffineFiniteProjectiveQuotient318
open AlgebraicGeometry CategoryTheory
open AffineWholeQuotientProjection318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
  {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of (S ⊗[R] A))) [IsClosedImmersion f]
  [IsFinite (projection R A S f)] [Flat (projection R A S f)]
  [LocallyOfFinitePresentation (projection R A S f)]
instance quotient_finite : IsFinite (quotientProjection R A S f) := by rw [← inverse_projection]; infer_instance
instance quotient_flat : Flat (quotientProjection R A S f) := by rw [← inverse_projection]; infer_instance
instance quotient_presentation : LocallyOfFinitePresentation (quotientProjection R A S f) := by
  rw [← inverse_projection]; infer_instance
instance finite : Module.Finite S (quotient R A S f) := by
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff _).mp
  rw [spec_coefficient]
  infer_instance
instance flat : Module.Flat S (quotient R A S f) := by
  apply RingHom.flat_algebraMap_iff.mp
  apply Flat.SpecMap_iff.mp
  rw [spec_coefficient]
  infer_instance
instance algebraPresentation : Algebra.FinitePresentation S (quotient R A S f) := by
  apply RingHom.finitePresentation_algebraMap.mp
  apply LocallyOfFinitePresentation.SpecMap_iff.mp
  rw [spec_coefficient]
  infer_instance
instance modulePresentation : Module.FinitePresentation S (quotient R A S f) :=
  Module.FinitePresentation.of_finite_of_finitePresentation S _
instance projective : Module.Projective S (quotient R A S f) :=
  FiniteProjectiveDualFrame318.projective_of_finitePresentation_flat S _
lemma rank_eq (x : PrimeSpectrum S) : Module.rankAtStalk (quotient R A S f) x=(projection R A S f).finrank x := by
  calc
    _ = (Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A S f)))).finrank x :=
      (Scheme.Hom.finrank_SpecMap_algebraMap S (quotient R A S f) x).symm
    _ = (quotientProjection R A S f).finrank x := congrArg (fun k => k.finrank x) (spec_coefficient R A S f)
    _ = _ := by rw [← inverse_projection,Scheme.Hom.finrank_comp_left_of_isIso]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
  (h : ∀ x : PrimeSpectrum S,(projection R A S f).finrank x=Fintype.card ι)
/-- The module-theoretic quotient input is DERIVED from the actual closed
finite-flat finitely presented family and its true structural rank. -/
@[expose] def data : VaryingProjectiveQuotientEquiv318.ProjectiveIdeal R A ι S :=
  ⟨ideal R A S f,inferInstance,inferInstance,fun x => (rank_eq R A S f x).trans (h x)⟩
end AffineFiniteProjectiveQuotient318
