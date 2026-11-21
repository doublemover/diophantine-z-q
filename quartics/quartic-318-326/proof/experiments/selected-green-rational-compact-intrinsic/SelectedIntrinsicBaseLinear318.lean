module
public import IntrinsicDifferentialIso318
public import IntrinsicDifferentialGlobalScalars318
public import Mathlib.LinearAlgebra.Basis.Basic
public section
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace SelectedIntrinsicBaseLinear318
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The constant functions from exactly the specified scheme structure,
before any affine localization. -/
@[expose] def constants (p : X ⟶ Spec (CommRingCat.of R)) : R →+* Γ(X,⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop).hom

/-- The actual global relative differentials, with their module over the
base ring restricted from the actual global-regular-function action. -/
@[expose] def Sections (p : X ⟶ Spec (CommRingCat.of R)) : Type u :=
  Γ(FamilyIntrinsicDifferentials318.omega p,⊤)

instance instAddCommGroup (p : X ⟶ Spec (CommRingCat.of R)) : AddCommGroup (Sections p) := by
  unfold Sections
  infer_instance

instance instModule (p : X ⟶ Spec (CommRingCat.of R)) : Module R (Sections p) := by
  unfold Sections
  exact Module.compHom _ (constants p)

variable (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
variable (e : X ≅ Y) (he : e.hom ≫ q = p)

theorem constants_pullback (a : R) : e.hom.appTop (constants q a) = constants p a := by
  have h : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop) ≫ e.hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop := by
    rw [Category.assoc,←Scheme.Hom.comp_appTop,he]
  exact congrArg (fun f => f a) h

/-- Pull back the actual global basis along the given scheme isomorphism,
with exactly the original base action on both sides. -/
@[expose] def linearPullback : Sections q ≃ₗ[R] Sections p where
  toFun := IntrinsicDifferentialIso318.globalEquiv e p q he
  invFun := (IntrinsicDifferentialIso318.globalEquiv e p q he).symm
  left_inv := (IntrinsicDifferentialIso318.globalEquiv e p q he).left_inv
  right_inv := (IntrinsicDifferentialIso318.globalEquiv e p q he).right_inv
  map_add' := (IntrinsicDifferentialIso318.globalEquiv e p q he).map_add
  map_smul' a ω := by
    change IntrinsicDifferentialPullback318.globalSection e.hom p q he (constants q a • ω) =
      constants p a • IntrinsicDifferentialPullback318.globalSection e.hom p q he ω
    rw [IntrinsicDifferentialGlobalScalars318.globalSection_smul,constants_pullback p q e he]

theorem linearPullback_apply (ω : Sections q) :
    linearPullback p q e he ω = IntrinsicDifferentialPullback318.globalSection e.hom p q he ω := rfl

@[expose] def transportedBasis {ι : Type u} (b : Module.Basis ι R (Sections q)) :
    Module.Basis ι R (Sections p) := b.map (linearPullback p q e he)

theorem transportedBasis_apply {ι : Type u} (b : Module.Basis ι R (Sections q)) (i : ι) :
    transportedBasis p q e he b i = IntrinsicDifferentialPullback318.globalSection e.hom p q he (b i) := by
  rw [transportedBasis,Module.Basis.map_apply,linearPullback_apply]

end SelectedIntrinsicBaseLinear318

#print axioms SelectedIntrinsicBaseLinear318.linearPullback
#print axioms SelectedIntrinsicBaseLinear318.transportedBasis_apply
