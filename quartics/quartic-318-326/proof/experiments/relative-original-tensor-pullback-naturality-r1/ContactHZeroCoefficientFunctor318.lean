module
public import ContactHZeroGeometricUnit318
public import ContactDerivedCoefficientFunctor318
public section
noncomputable section
namespace ContactHZeroCoefficientFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

/-- Actual H1 vanishing is preserved for the literal original pulled
line under arbitrary affine coefficient change, not only flat maps. -/
lemma vanishing (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0) :
    ∀ x : NonreducedLineMayerVietoris318.H1 (L' R S f c L),x=0 := by
  letI : Module R (NonreducedLineMayerVietoris318.H1 L) :=
    OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
  letI : Module S (NonreducedLineMayerVietoris318.H1 (L' R S f c L)) :=
    OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c) _ 1
  intro x
  let e := ContactOriginalHOneBaseChange318.equivalence R S f c L
  obtain ⟨z,rfl⟩ := e.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul s y => rw [hz y,tmul_zero,map_zero]
  | add z w hz hw => rw [map_add,hz,hw,add_zero]

lemma pull_smul (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
    (r : R) (x : Γ(L.object,⊤)) :
    pull (curveMap R S f c) L.object (r • x) = f r • pull (curveMap R S f c) L.object x := by
  have ht : (1:S) ⊗ₜ[R] (r • x) = f r ⊗ₜ[R] x := by
    rw [tmul_smul,smul_tmul']
    congr 1
    change f r * 1 = f r
    exact mul_one _
  rw [← ContactHZeroGeometricUnit318.unit R c L S f hz,ht,
    ContactHZeroGeometricUnit318.pure_tensor]

variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : S →ₐ[ℚ] T)
local instance : Algebra S T := g.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local instance (N : Line (curve T c)) : Module T Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule T (ContactRelativeStructuralHOne318.projection T c) N ⊤

@[expose] def coefficientArrow : S →ₐ[R] T where
  __ := g.toRingHom
  commutes' r := rfl

@[expose] def transport : S ⊗[R] Γ(L.object,⊤) →ₗ[R] T ⊗[R] Γ(L.object,⊤) :=
  TensorProduct.map (coefficientArrow R S f T g).toLinearMap LinearMap.id

/-- The actual composition sheaf comparison on GLOBAL sections is
structural-coefficient linear; it is not chosen by a Cech presentation. -/
@[expose] def compositionSections :
    Γ((L' S T g c (L' R S f c L)).object,⊤) →ₗ[T] Γ((L' R T (g.comp f) c L).object,⊤) where
  __ := ((ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app ⊤).hom
  map_smul' t x := by
    change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app ⊤
      (OriginalCoefficientCohomology318.scalar T (ContactRelativeStructuralHOne318.projection T c) ⊤ t • x) = _
    exact Scheme.Modules.Hom.app_smul _ _ _

lemma geometric_composition (x : Γ(L.object,⊤)) :
    compositionSections R S f c L T g
      (pull (curveMap S T g c) (L' R S f c L).object (pull (curveMap R S f c) L.object x)) =
      pull (curveMap R T (g.comp f) c) L.object x :=
  OriginalSectionPullbackComposition318.path (curveMap S T g c) (curveMap R S f c)
    (curveMap R T (g.comp f) c) (ContactCoefficientWholeOpens318.composition R S f c T g) L.object x

/-- Genuine geometric pullback of the actual tensor-H0 realization
commutes with arbitrary coefficient specialization on EVERY tensor, with
the original line associator and literal coefficient map. -/
lemma specialize (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
    (z : S ⊗[R] Γ(L.object,⊤)) :
    compositionSections R S f c L T g
      (pull (curveMap S T g c) (L' R S f c L).object
        (ContactRelativeHZeroBaseChange318.equivalence R S f c L hz z)) =
    ContactRelativeHZeroBaseChange318.equivalence R T (g.comp f) c L hz
      (transport R S f c L T g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    rw [ContactHZeroGeometricUnit318.pure_tensor,
      pull_smul S T g c (L' R S f c L) (vanishing R S f c L hz),map_smul,geometric_composition]
    change g s • pull (curveMap R T (g.comp f) c) L.object x =
      ContactRelativeHZeroBaseChange318.equivalence R T (g.comp f) c L hz (g s ⊗ₜ[R] x)
    exact (ContactHZeroGeometricUnit318.pure_tensor R c L T (g.comp f) hz (g s) x).symm
  | add z w hz hw => simp only [map_add,hz,hw]
end ContactHZeroCoefficientFunctor318
