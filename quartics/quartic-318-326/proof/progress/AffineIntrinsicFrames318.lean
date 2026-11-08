module
public import AffineIntrinsicIso318
public import InvariantNormalizedFrames318
public section
noncomputable section
namespace AffineIntrinsicFrames318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- The affine coefficient map is the one extracted from the actual Spec
morphism, not an independently chosen algebra structure. -/
theorem coefficients_specMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    FamilyIntrinsicDifferentials318.coefficients (Spec.map f) =
      AffineIntrinsicComparison318.coefficients f := by
  unfold FamilyIntrinsicDifferentials318.coefficients AffineIntrinsicComparison318.coefficients
  rw [←Scheme.ΓSpecIso_inv_naturality]

@[expose] def specMapIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    tilde (CommRingCat.KaehlerDifferential f) ≅
      FamilyIntrinsicDifferentials318.omega (Spec.map f) :=
  AffineIntrinsicIso318.iso f ≪≫ eqToIso (by
    unfold AffineIntrinsicComparison318.omega FamilyIntrinsicDifferentials318.omega
    rw [coefficients_specMap])

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Preserve the given algebra instance when relating categorical and ordinary
Kähler modules. -/
theorem module_eq :
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap R S)) =
      ModuleCat.of S (KaehlerDifferential R S) := by
  exact congrArg (fun (α : Algebra R S) =>
    letI := α
    ModuleCat.of S (KaehlerDifferential R S)) (toAlgebra_algebraMap (R:=R) (S:=S))

/-- The actual affine differential sheaf agrees with the intrinsic universal
sheaf for the actual structural map. -/
@[expose] def algebraIso :
    AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S) ≅
      FamilyIntrinsicDifferentials318.omega
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (tilde.functor (CommRingCat.of S)).mapIso (eqToIso module_eq.symm) ≪≫
    specMapIso (CommRingCat.ofHom (algebraMap R S))

/-- A proved algebraic frame trivializes the intrinsic differential sheaf on
the actual affine scheme. No intrinsic frame is supplied as a hypothesis. -/
@[expose] def frameIso (frame : KaehlerDifferential R S ≃ₗ[S] S) :
    FamilyIntrinsicDifferentials318.omega
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
        SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  algebraIso.symm ≪≫ AffineDifferentialSheaf318.frameIso frame

variable (A B : R)

/-- Intrinsic relative differentials on the actual x-Jacobian affine chart. -/
@[expose] def xFrameIso := frameIso (InvariantNormalizedFrames318.xFrame A B)
/-- Intrinsic relative differentials on the actual y-Jacobian affine chart. -/
@[expose] def finiteFrameIso := frameIso (InvariantNormalizedFrames318.finiteFrame A B)
/-- Intrinsic relative differentials on the actual infinity affine chart. -/
@[expose] def infinityFrameIso := frameIso (InvariantNormalizedFrames318.infinityFrame A B)
end AffineIntrinsicFrames318
