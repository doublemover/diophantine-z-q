module
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.LocalRing.Module
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedCanonicalFiniteAffine318

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (CommRingCat.of R)) [IsFinite p]

/-- Literal global sections, not a chosen isomorphic order. -/
abbrev coord (X : Scheme.{u}) := Scheme.Γ.obj (Opposite.op X)

/-- Canonical affine equivalence of the very same finite scheme. -/
def model : Spec (coord X) ≅ X := by
  letI : IsAffine X := isAffine_of_isAffineHom p
  exact X.isoSpec.symm

private def ringArrow : CommRingCat.of R ⟶ coord X :=
  (Scheme.Spec.preimage ((model p).hom ≫ p)).unop

private theorem spec_arrow : Spec.map (ringArrow p) = (model p).hom ≫ p :=
  Scheme.Spec.map_preimage ((model p).hom ≫ p)

/-- Coefficient structure pulled back by the actual morphism p. -/
def coefficients : Algebra R (coord X) := (ringArrow p).hom.toAlgebra

theorem model_over :
    letI : Algebra R (coord X) := coefficients p
    (model p).hom ≫ p = Spec.algebraMap R (coord X) := by
  letI : Algebra R (coord X) := coefficients p
  change (model p).hom ≫ p = Spec.map (ringArrow p)
  exact (spec_arrow p).symm

theorem finite :
    letI : Algebra R (coord X) := coefficients p
    Module.Finite R (coord X) := by
  letI : Algebra R (coord X) := coefficients p
  have h : IsFinite (Spec.map (ringArrow p)) := by
    rw [spec_arrow]
    infer_instance
  apply RingHom.finite_algebraMap.mp
  exact (IsFinite.SpecMap_iff (ringArrow p)).mp h

theorem flat [Flat p] :
    letI : Algebra R (coord X) := coefficients p
    Module.Flat R (coord X) := by
  letI : Algebra R (coord X) := coefficients p
  have h : Flat (Spec.map (ringArrow p)) := by
    rw [spec_arrow]
    infer_instance
  apply RingHom.flat_algebraMap_iff.mp
  exact Flat.SpecMap_iff.mp h

/-- In particular this is the actual finite free algebra over the
selected height-one local base, even with nonreduced bad fibers. -/
theorem free_over_local [Flat p] [IsLocalRing R] :
    letI : Algebra R (coord X) := coefficients p
    Module.Free R (coord X) := by
  letI : Algebra R (coord X) := coefficients p
  letI : Module.Finite R (coord X) := finite p
  letI : Module.Flat R (coord X) := flat p
  exact Module.free_of_flat_of_isLocalRing

end SelectedCanonicalFiniteAffine318

#print axioms SelectedCanonicalFiniteAffine318.model_over
#print axioms SelectedCanonicalFiniteAffine318.free_over_local
