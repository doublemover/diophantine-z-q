module
public import SquareZeroFramedReduction318
public import OriginalLineAffineBaseChange318
public import LineSheafUnit318
public import Mathlib.RingTheory.Flat.EquationalCriterion
public section
noncomputable section
namespace OriginalAffineSquareZeroFrame318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{u})
/-- The exact unit sections comparison, through the original tilde unit and
literal tilde of the coefficient ring, with no arbitrary module equivalence. -/
@[expose] def unitSections : moduleSpecΓFunctor.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅
    ModuleCat.of R R :=
  moduleSpecΓFunctor.mapIso (tildeSelf (R := R)).symm ≪≫
    (tilde.isoTop (ModuleCat.of R R)).symm
variable {S R : CommRingCat.{u}} (f : S ⟶ R) (L : LineSheafClass318.Line (Spec S))
    (t : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
@[expose] def reducedFrame :
    (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections S L) ≃ₗ[R] R :=
  (OriginalLineAffineBaseChange318.sectionsIso f L ≪≫ moduleSpecΓFunctor.mapIso t ≪≫ unitSections R).toLinearEquiv
variable (σ : R →+* S) (hσ : ∀ r, f (σ r) = r) (e : S) (he : e * e = 0)
    (hker : RingHom.ker f.hom = Ideal.span {e})
/-- A genuine frame of the ORIGINAL affine line, constructed from the actual
special-fiber frame, canonical global sections, literal scalar extension and
square-zero generator lifting. No affine Picard invariance is assumed. -/
@[expose] def frame : SheafOfModules.unit (Spec S).ringCatSheaf ≅ L.object := by
  letI : Algebra S R := f.hom.toAlgebra
  let P := OriginalLineAffineModel318.sections S L
  letI : Module.FinitePresentation S P := (OriginalLineAffineModel318.properties S L).1
  letI : Module.Flat S P := (OriginalLineAffineModel318.properties S L).2.1
  letI : Module.Projective S P := Module.Flat.projective_of_finitePresentation
  let b : S ≃ₗ[S] P := SquareZeroFramedReduction318.equivalence σ hσ e he hker (reducedFrame f L t)
  exact (tildeSelf (R := S)).symm ≪≫ (tilde.functor S).mapIso b.toModuleIso ≪≫
    OriginalLineAffineModel318.canonicalIso S L
include t hσ he hker in
lemma class_trivial : LineSheafClass318.classOf L = LineSheafUnit318.unitClass (Spec S) :=
  LineSheafClass318.classOf_eq (frame f L t σ hσ e he hker).symm
end OriginalAffineSquareZeroFrame318
