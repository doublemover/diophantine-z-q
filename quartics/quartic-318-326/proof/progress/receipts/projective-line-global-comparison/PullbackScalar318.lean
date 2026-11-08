module
public import ClutchedModule318
public import ModuleTopExt318
public import IdentityCotangent318
public section
noncomputable section
namespace PullbackScalar318
open AlgebraicGeometry CategoryTheory
open ClutchedModule318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (a : Γ(Y,⊤))

theorem multiply_unitMap : multiply a ≫ StructurePushforwardSplit318.unitMap p=
    StructurePushforwardSplit318.unitMap p ≫ (Scheme.Modules.pushforward p).map (multiply (p.appTop a)) := by
  apply ModuleTopExt318.ext
  change p.appTop ((multiply a).app ⊤ (show Γ(Y,⊤) from 1))=(multiply (p.appTop a)).app ⊤ (p.appTop 1)
  rw [multiply_top,multiply_top,one_mul,map_one,one_mul]

theorem adjoint_unit : (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
    (IdentityCotangent318.pullbackUnitIso p).hom=StructurePushforwardSplit318.unitMap p :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit p.toRingCatSheafHom

/-- Pulling back scalar multiplication gives the literal pullback regular function,
under the same canonical unit comparison used for the pulled coordinate sections. -/
theorem pullback_multiply :
    (Scheme.Modules.pullback p).map (multiply a) ≫ (IdentityCotangent318.pullbackUnitIso p).hom=
      (IdentityCotangent318.pullbackUnitIso p).hom ≫ multiply (p.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right,adjoint_unit]
  exact multiply_unitMap p a
end PullbackScalar318
