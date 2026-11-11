module
public import OriginalCoefficientCohomology318
public import OriginalOpenPullbackSectionScalar318
public section
noncomputable section
namespace OriginalCoefficientImageScalar318
open AlgebraicGeometry CategoryTheory
open OriginalCoefficientCohomology318
variable (R B : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R)
  (f : Spec B ⟶ X) [IsOpenImmersion f] (g : R ⟶ B)
  (h : f ≫ p = Spec.map g)

include h in
/-- Actual structural coefficients, through the original full-image ring
comparison. Both the original structure-map equation and ΓSpec naturality
are used; no coefficient action is transported by an arbitrary equivalence. -/
lemma image_scalar (r : R) :
    (f.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (g r)) =
      scalar R p (f ''ᵁ ⊤) r := by
  have hn := congrArg (fun q => q r) (Scheme.ΓSpecIso_inv_naturality g)
  have hp := congrArg (fun q => q.appTop ((Scheme.ΓSpecIso R).inv r)) h
  simp only [Scheme.Hom.comp_appTop,ConcreteCategory.comp_apply] at hp
  have hi := congrArg (fun q => q (p.appTop ((Scheme.ΓSpecIso R).inv r)))
    (f.app_appIso_inv ⊤)
  calc
    (f.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (g r)) =
        (f.appIso ⊤).inv (f.appTop (p.appTop ((Scheme.ΓSpecIso R).inv r))) :=
      congrArg (f.appIso ⊤).inv (hn.trans hp.symm)
    _ = scalar R p (f ''ᵁ ⊤) r := hi
end OriginalCoefficientImageScalar318
