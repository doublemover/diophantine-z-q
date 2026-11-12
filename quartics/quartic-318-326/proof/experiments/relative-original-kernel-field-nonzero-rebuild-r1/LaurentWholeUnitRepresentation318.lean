module
public import WholeAffineTargetFunctions318
public import LaurentCoefficientUnitPoints318
public import ContactOriginalStabilizerUnitPresheaf318
public section
noncomputable section
namespace LaurentWholeUnitRepresentation318
open AlgebraicGeometry CategoryTheory Opposite
variable (R : CommRingCat.{0})
abbrev ring := CommRingCat.of (LaurentPolynomial R)
abbrev scheme := Spec (ring R)
abbrev projection : scheme R ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
/-- Exact Over-point/ring-map comparison, using global functions on the ENTIRE test. -/
@[expose] def coefficientPoints (T : Over (Spec R)) :
    (T ⟶ Over.mk (projection R)) ≃
      LaurentCoefficientUnitPoints318.Points (WholeAffineTargetFunctions318.ringMap R T.hom).hom where
  toFun a := ⟨(WholeAffineTargetFunctions318.ringMap (ring R) a.left).hom,by
    have h := congrArg (WholeAffineTargetFunctions318.ringMap R) a.w
    rw [WholeAffineTargetFunctions318.target] at h
    exact congrArg CommRingCat.Hom.hom h⟩
  invFun a := Over.homMk
    (WholeAffineTargetFunctions318.realize (ring R) (CommRingCat.ofHom a.val)) (by
      apply (WholeAffineTargetFunctions318.equivalence R).injective
      change WholeAffineTargetFunctions318.ringMap R (_ ≫ projection R)=_
      rw [WholeAffineTargetFunctions318.target,WholeAffineTargetFunctions318.ringMap_realize]
      exact CommRingCat.hom_ext a.property)
  left_inv a := by
    apply Over.OverMorphism.ext
    exact (WholeAffineTargetFunctions318.equivalence (ring R)).symm_apply_apply a.left
  right_inv a := by
    apply Subtype.ext
    exact congrArg CommRingCat.Hom.hom
      (WholeAffineTargetFunctions318.ringMap_realize (ring R) (CommRingCat.ofHom a.val))
@[expose] def points (T : Over (Spec R)) : (T ⟶ Over.mk (projection R)) ≃ Γ(T.left,⊤)ˣ :=
  (coefficientPoints R T).trans (LaurentCoefficientUnitPoints318.equivalence _)
lemma natural {T U : Over (Spec R)} (h : U ⟶ T) (a : T ⟶ Over.mk (projection R)) :
    points R U (h ≫ a)=Units.map h.left.appTop.hom.toMonoidHom (points R T a) := by
  apply Units.ext
  change (WholeAffineTargetFunctions318.ringMap (ring R) (h.left ≫ a.left))
      (LaurentPolynomial.T 1)=_
  rw [WholeAffineTargetFunctions318.source]
  rfl
/-- Literal Laurent Spec represents base units, for all nonaffine and nilpotent tests. -/
@[expose] def representation : yoneda.obj (Over.mk (projection R)) ≅
    ContactOriginalStabilizerUnitPresheaf318.unitsPresheaf R :=
  NatIso.ofComponents (fun T => Equiv.toIso (points R T.unop)) (by
    intro T U h
    funext a
    exact natural R h.unop a)

end LaurentWholeUnitRepresentation318
