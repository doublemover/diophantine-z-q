module
public import SymmetricPrimitiveRegular318
public import ProjectiveSectionParameter318
public import SectionZeroRegularCoordinate318
public section
noncomputable section
namespace UniversalPrimitiveCoordinate318
open scoped TensorProduct
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
  (ell : Module.Dual R P) (s : P) (hs : ell s=1)

@[expose] def evaluate : Module.Dual R P →ₗ[R] R where
  toFun f := f s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal coordinate of the SAME universal tensor section is
regular whenever the evaluation coordinate has an actual section of value
one. This is a primitive-coordinate theorem, NOT an assertion that all
specialized sections or all parameter fibers are regular. -/
theorem regular (a : ProjectiveSectionParameter318.algebra R P)
    (ha : a * FiniteProjectiveTensorDual318.pairing R P
      (ProjectiveSectionParameter318.algebra R P)
      (ProjectiveSectionParameter318.universal R P) ell = 0) : a=0 := by
  rw [ProjectiveSectionParameter318.universal_coordinate] at ha
  exact SymmetricPrimitiveRegular318.generator_regular R (Module.Dual R P)
    (evaluate R P s) ell hs a ha
end UniversalPrimitiveCoordinate318
