module
public import AffineIntrinsicFrames318
public import FamilyOpenRestriction318
public section
noncomputable section
namespace IntrinsicEqualityTransport318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- Equal coefficient maps identify their universal differential derivations,
not only their underlying sheaf objects. -/
theorem omega_eq_D {X : Scheme.{u}} {C : X.Opensᵒᵖ ⥤ CommRingCat.{u}}
    {φ ψ : C ⟶ X.presheaf} (h : φ=ψ) {U : X.Opensᵒᵖ} (s : X.presheaf.obj U) :
    (eqToIso (congrArg UniversalSheafDifferentials318.omega h)).hom.val.app U
      ((UniversalSheafDifferentials318.D φ).d s) =
        (UniversalSheafDifferentials318.D ψ).d s := by
  subst ψ
  rfl

variable {R S : Type u} [CommRing R] [CommRing S]

@[expose] def algebraModule (α : Algebra R S) : ModuleCat S :=
  letI := α
  ModuleCat.of S (KaehlerDifferential R S)
@[expose] def algebraD (α : Algebra R S) (s : S) : algebraModule α :=
  letI := α
  KaehlerDifferential.D R S s

/-- Transporting algebra structures by equality also transports the literal
universal differential. -/
theorem algebra_eq_D {α β : Algebra R S} (h : α=β) (s : S) :
    (eqToIso (congrArg algebraModule h)).hom (algebraD α s) = algebraD β s := by
  subst β
  rfl

variable [Algebra R S]
theorem categorical_D (s : S) :
    (eqToIso (AffineIntrinsicFrames318.module_eq (R:=R) (S:=S))).hom
      (CommRingCat.KaehlerDifferential.d (f:=CommRingCat.ofHom (algebraMap R S)) s) =
        KaehlerDifferential.D R S s :=
  algebra_eq_D (toAlgebra_algebraMap (R:=R) (S:=S)) s
end IntrinsicEqualityTransport318
