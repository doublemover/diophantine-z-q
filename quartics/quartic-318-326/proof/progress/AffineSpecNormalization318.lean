module
public import IntrinsicEqualityTransport318
public section
noncomputable section
namespace AffineSpecNormalization318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Keep an affine comparison together with its exact universal-differential
normalization, so coefficient equality transports the complete datum. -/
structure Data (φ : (Functor.const (Spec S).Opensᵒᵖ).obj R ⟶ (Spec S).presheaf) where
  iso : tilde (CommRingCat.KaehlerDifferential f) ≅ UniversalSheafDifferentials318.omega φ
  fac (s : S) : moduleSpecΓFunctor.map iso.hom
      ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
        (CommRingCat.KaehlerDifferential.d s)) =
    (UniversalSheafDifferentials318.D φ).d ((Scheme.ΓSpecIso S).inv s)

@[expose] def affineData : Data f (AffineIntrinsicComparison318.coefficients f) :=
  ⟨AffineIntrinsicIso318.iso f,AffineIntrinsicIso318.iso_global_D f⟩

/-- Actual structure coefficients are transported together with the proved
normalization, avoiding an unnormalized choice of affine frame. -/
@[expose] def specData : Data f (FamilyIntrinsicDifferentials318.coefficients (Spec.map f)) :=
  (AffineIntrinsicFrames318.coefficients_specMap f).symm ▸ affineData f

@[expose] def specIso : tilde (CommRingCat.KaehlerDifferential f) ≅
    FamilyIntrinsicDifferentials318.omega (Spec.map f) := (specData f).iso

theorem specMap_D (s : S) :
    moduleSpecΓFunctor.map (specIso f).hom
      ((tilde.isoTop (CommRingCat.KaehlerDifferential f)).hom
        (CommRingCat.KaehlerDifferential.d s)) =
    (FamilyIntrinsicDifferentials318.D (Spec.map f)).d ((Scheme.ΓSpecIso S).inv s) :=
  (specData f).fac s
end AffineSpecNormalization318
