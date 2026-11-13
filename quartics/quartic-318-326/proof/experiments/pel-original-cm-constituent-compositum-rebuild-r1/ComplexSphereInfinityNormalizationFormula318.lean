module
public import ComplexSphereInfinityQuadruple318
public import ProjectiveLineActualAutomorphismPoints318
public section
noncomputable section
namespace ComplexSphereInfinityNormalizationFormula318
open AlgebraicGeometry CategoryTheory
open ComplexSphereFourPointNormalization318 ComplexSphereInfinityQuadruple318
open ComplexSphereAffineAutomorphisms318 ProjectiveLineComplexSchemePoints318
open scoped OnePoint

/-- The old choice-defined normalization on the ENTIRE sphere is the
literal affine formula when its specified first point is infinity. -/
lemma normalization_eq (a b c:ℂ)
    (h:Function.Injective (![∞,(a:ℂ),(b:ℂ),(c:ℂ)]:Fin 4→OnePoint ℂ))
    (hab:b-a≠0) (z:OnePoint ℂ):
    normalization ![∞,(a:ℂ),(b:ℂ),(c:ℂ)] h z=
      affineSphere (b-a)⁻¹ (-a/(b-a)) (inv_ne_zero hab) z:=by
  simp only [normalization,Homeomorph.trans_apply,finite_coordinate,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

/-- Equality of actual Spec-C-valued scheme maps with that SAME analytic
normalization, including infinity. No curve comparison is presumed. -/
theorem actual_scheme_normalization (a b c:ℂ)
    (h:Function.Injective (![∞,(a:ℂ),(b:ℂ),(c:ℂ)]:Fin 4→OnePoint ℂ))
    (hab:b-a≠0) (z:OnePoint ℂ):
    (spherePoint z).val≫(ProjectiveAffineLine318.iso ℂ
      (Units.mk0 (b-a)⁻¹ (inv_ne_zero hab)) (-a/(b-a))).hom=
        (spherePoint (normalization ![∞,(a:ℂ),(b:ℂ),(c:ℂ)] h z)).val:=by
  rw [normalization_eq a b c h hab z]
  exact ProjectiveLineActualAutomorphismPoints318.affine_sphere _ _ z
end ComplexSphereInfinityNormalizationFormula318
