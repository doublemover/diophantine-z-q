module
public import IntegralRetraction318
public import CompletedIntegral318
public import CubicClosedImmersion318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section
noncomputable section
namespace ProperGlobalSections318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}
set_option maxHeartbeats 600000

/-- A proper integral scheme with a section has no extra global functions over
an integral affine base. No geometric-fiber or normality assumption is needed. -/
theorem appTop_bijective [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (p : X ⟶ Y) [UniversallyClosed p] (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) :
    Function.Bijective p.appTop := by
  apply IntegralRetraction318.bijective p.appTop.hom e.appTop.hom
    (isIntegral_appTop_of_universallyClosed p)
  have h : p.appTop ≫ e.appTop = 𝟙 _ := by rw [←Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  exact congrArg CommRingCat.Hom.hom h

variable {R : Type u} [CommRing R] [IsDomain R]
/-- Actual global functions on the completed short Weierstrass family are
exactly those on its domain base, by the actual infinity section. -/
theorem family_appTop_bijective (A B : R) :
    Function.Bijective (WeierstrassGluing318.structureMap A B).appTop := by
  letI := CompletedIntegral318.completed_integral A B
  letI := CubicClosedImmersion318.structure_proper A B
  exact appTop_bijective _ _ (WeierstrassGluing318.infinity_section A B)
end ProperGlobalSections318
