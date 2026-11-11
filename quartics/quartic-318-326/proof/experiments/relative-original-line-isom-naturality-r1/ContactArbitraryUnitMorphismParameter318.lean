module
public import ContactArbitrarySectionSpecialization318
public import ModuleTopExt318
public section
noncomputable section
namespace ContactArbitraryUnitMorphismParameter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The actual whole O-linear morphism is recovered from its value on one. -/
@[expose] def sectionEquiv {X : Scheme.{u}} (M : X.Modules) :
    Γ(M,⊤) ≃ (SheafOfModules.unit X.ringCatSheaf ⟶ M) where
  toFun := ModuleGlobalSections318.ofTop M
  invFun a := a.app ⊤ 1
  left_inv := ModuleTopMorphisms318.ofTop_top_one
  right_inv a := (ModuleTopExt318.eq_ofTop a).symm

variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra

/-- The same actual affine algebra classifies genuine morphisms from the structure
sheaf into the literal pulled original line on every affine coefficient test.
It does not replace isomorphisms by nonzero sections or assert an isomorphism locus. -/
@[expose] def points : (parameterRing R c L →ₐ[R] S) ≃
    (SheafOfModules.unit (curve S c).ringCatSheaf ⟶ (L' R S f c L).object) :=
  (ContactArbitrarySectionParameter318.points R c L S f).trans
    (sectionEquiv (L' R S f c L).object)

lemma value (a : parameterRing R c L →ₐ[R] S) :
    (points R c L S f a).app ⊤ 1 = ContactArbitrarySectionParameter318.points R c L S f a :=
  ModuleTopMorphisms318.ofTop_top_one _
end ContactArbitraryUnitMorphismParameter318
