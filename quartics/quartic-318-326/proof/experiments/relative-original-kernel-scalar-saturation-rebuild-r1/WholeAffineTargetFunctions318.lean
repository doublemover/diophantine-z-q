module
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public section
noncomputable section
namespace WholeAffineTargetFunctions318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} (A : CommRingCat.{u})
/-- The actual structural ring map of a map from ANY whole scheme to an affine target. -/
@[expose] def ringMap (f : X ⟶ Spec A) : A ⟶ Γ(X,⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ f.appTop
@[expose] def realize (a : A ⟶ Γ(X,⊤)) : X ⟶ Spec A :=
  (ΓSpec.adjunction.homEquiv X (op A)) a.op
lemma ringMap_realize (a : A ⟶ Γ(X,⊤)) : ringMap A (realize A a)=a :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv a
@[expose] def equivalence : (X ⟶ Spec A) ≃ (A ⟶ Γ(X,⊤)) where
  toFun := ringMap A
  invFun := realize A
  left_inv f := by
    apply ext_to_Spec
    exact ringMap_realize A (ringMap A f)
  right_inv := ringMap_realize A
lemma source (h : Y ⟶ X) (f : X ⟶ Spec A) :
    ringMap A (h ≫ f)=ringMap A f ≫ h.appTop := by
  simp only [ringMap,Scheme.Hom.comp_appTop,Category.assoc]
lemma target {B : CommRingCat.{u}} (a : B ⟶ A) (f : X ⟶ Spec A) :
    ringMap B (f ≫ Spec.map a)=a ≫ ringMap A f := by
  simp only [ringMap,Scheme.Hom.comp_appTop]
  rw [←Category.assoc,←Scheme.ΓSpecIso_inv_naturality,Category.assoc]

end WholeAffineTargetFunctions318
