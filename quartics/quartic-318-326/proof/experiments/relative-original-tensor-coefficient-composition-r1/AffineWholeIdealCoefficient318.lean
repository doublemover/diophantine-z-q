module
public import VaryingFlatPrincipalRegular318
public section
noncomputable section
namespace AffineWholeIdealCoefficient318
open AlgebraicGeometry CategoryTheory
open AffineWholeQuotientProjection318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of (S ⊗[R] A))) [IsClosedImmersion f]
  [IsFinite (projection R A S f)] [Flat (projection R A S f)]
  [LocallyOfFinitePresentation (projection R A S f)]
/-- Standard geometric properties of the ACTUAL whole closed family
supply the quotient-flat input for full ideal-module base change. -/
@[expose] def equivalence : T ⊗[S] ideal R A S f ≃ₗ[T]
    VaryingWholeQuotientTensor318.ideal R A S T (ideal R A S f) :=
  VaryingFlatIdealCoefficient318.equivalence R A S T (ideal R A S f)
lemma unit_tmul (i : ideal R A S f) : (equivalence R A S T f ((1 : T) ⊗ₜ[S] i)).val=
    VaryingWholeQuotientTensor318.source R A S T i.val :=
  VaryingFlatIdealCoefficient318.unit_tmul R A S T (ideal R A S f) i
/-- Regularity is transported for a supplied actual principal chart;
this does NOT assert that every whole Hilbert ideal already has one. -/
lemma principal_regular (c : S ⊗[R] A) (hI : ideal R A S f=Ideal.span ({c} : Set (S ⊗[R] A)))
    (hc : ∀ z : S ⊗[R] A,z*c=0 → z=0) :
    ∀ z : T ⊗[R] A,z*VaryingWholeQuotientTensor318.source R A S T c=0 → z=0 := by
  letI : Module.Flat S ((S ⊗[R] A) ⧸ Ideal.span ({c} : Set (S ⊗[R] A))) :=
    hI ▸ (inferInstance : Module.Flat S (quotient R A S f))
  exact VaryingFlatPrincipalRegular318.regular R A S T c hc
end AffineWholeIdealCoefficient318
