module
public import PELOriginalLinePowerGauge318
public import LineSheafTensorPower318
public import Mathlib.Tactic.Group
public section
noncomputable section
namespace PELOriginalPolarizationCube318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The constructed degree-one sheaf is the actual tensor difference
of the SAME cubic and quadratic lines. This class equality is witnessed
by the identity on their genuine sheafified tensor objects. -/
lemma class_difference :
    classOf (line τ hτ) = classOf (cubicLine τ hτ) * (classOf (quadraticLine τ hτ))⁻¹ := by
  have he : classOf (line τ hτ) =
      classOf (LineSheafTensor318.line (cubicLine τ hτ)
        (FramedLineInverse318.inverse (quadraticLine τ hτ))) := classOf_eq (Iso.refl _)
  rw [he,LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse]

/-- The class relation is derived from the explicit whole-sheaf sixth
power isomorphism, not imposed from analytic Chern data. -/
lemma sixth_class : (classOf (cubicLine τ hτ))^2 = (classOf (quadraticLine τ hτ))^3 := by
  rw [←LineSheafTensorPower318.classOf_power,←LineSheafTensorPower318.classOf_power]
  exact classOf_eq (PELOriginalLinePowerGauge318.sixthPowerIso τ hτ).symm

lemma cube_class : classOf (LineSheafTensorPower318.line (line τ hτ) 3) =
    classOf (cubicLine τ hτ) := by
  rw [LineSheafTensorPower318.classOf_power,class_difference,mul_pow,inv_pow,←sixth_class]
  group

/-- A genuine algebraic isomorphism L tensor L tensor L ≅ H3, with
actual inverse morphisms. Existence is extracted from the quotient
whose defining relation is literal sheaf isomorphism, after proving
that relation using the explicit regular sixth-power gauge. -/
@[expose] def cubeIso :
    (LineSheafTensorPower318.line (line τ hτ) 3).object ≅ cubicSheaf τ hτ :=
  Classical.choice ((classOf_eq_iff _ _).mp (cube_class τ hτ))

lemma cube_hom_inv : (cubeIso τ hτ).hom ≫ (cubeIso τ hτ).inv = 𝟙 _ :=
  (cubeIso τ hτ).hom_inv_id
lemma cube_inv_hom : (cubeIso τ hτ).inv ≫ (cubeIso τ hτ).hom = 𝟙 _ :=
  (cubeIso τ hτ).inv_hom_id

/-- The square similarly recovers the unchanged quadratic line. Both
power identifications are algebraic and concern complete module sheaves. -/
lemma square_class : classOf (LineSheafTensorPower318.line (line τ hτ) 2) =
    classOf (quadraticLine τ hτ) := by
  rw [LineSheafTensorPower318.classOf_power,class_difference,mul_pow,inv_pow,sixth_class]
  group

@[expose] def squareIso :
    (LineSheafTensorPower318.line (line τ hτ) 2).object ≅ quadraticSheaf τ hτ :=
  Classical.choice ((classOf_eq_iff _ _).mp (square_class τ hτ))
lemma square_hom_inv : (squareIso τ hτ).hom ≫ (squareIso τ hτ).inv = 𝟙 _ :=
  (squareIso τ hτ).hom_inv_id
lemma square_inv_hom : (squareIso τ hτ).inv ≫ (squareIso τ hτ).hom = 𝟙 _ :=
  (squareIso τ hτ).inv_hom_id
end PELOriginalPolarizationCube318
