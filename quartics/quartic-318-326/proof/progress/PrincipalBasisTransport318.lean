module
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace PrincipalBasisTransport318
open Module
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {R:Type u} [CommRing R] {B:Type v} [CommRing B] [Algebra R B]
    (r:R) (R':Type w) [CommRing R'] [Algebra R R'] [IsLocalization.Away r R']
    (B':Type z) [CommRing B'] [Algebra B B'] [Algebra R' B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B']
    [IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) B']
/-- Transport a basis of the canonical localized module to the actual
localized coefficient and source rings, through their exact localization maps. -/
@[expose] def basis {ι:Type*}
    (b:Basis ι (Localization.Away r) (LocalizedModule.Away r B)):Basis ι R' B':=by
  let e:Localization.Away r≃ₐ[R]R':=IsLocalization.algEquiv (Submonoid.powers r) _ _
  letI:Algebra (Localization.Away r) B':=
    ((algebraMap R' B').comp e.toRingHom).toAlgebra
  letI:IsScalarTower R (Localization.Away r) B':=by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap R B' a=algebraMap R' B' (e (algebraMap R (Localization.Away r) a))
    rw [e.commutes,←IsScalarTower.algebraMap_apply R R' B']
  let f:B→ₗ[R]B':=(IsScalarTower.toAlgHom R B B').toLinearMap
  let eM:LocalizedModule.Away r B≃ₗ[Localization.Away r]B':=
    (IsLocalizedModule.iso (Submonoid.powers r) f).extendScalarsOfIsLocalization
      (Submonoid.powers r) (Localization.Away r)
  apply (b.map eM).mapCoeffs e.toRingEquiv
  intro a x
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rfl
end PrincipalBasisTransport318
