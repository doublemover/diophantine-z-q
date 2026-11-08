module
public import IntegralFractionComparison318
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public section
noncomputable section
namespace IntegralGenericIso318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsIntegralHom f] [IsDominant f]
    [IsIso (DominantFunctionField318.map f)]

/-- An actual integral generic-stalk isomorphism is an isomorphism over
any nonempty affine target open whose entire section ring is normal. -/
theorem app_isIso (U:Y.Opens) (hU:IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(Y,U)]:IsIso (f.app U):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:IsFractionRing Γ(Y,U) Y.functionField:=functionField_isFractionRing_of_isAffineOpen Y U hU
  let e:=asIso (DominantFunctionField318.map f)
  let j:Γ(X,f⁻¹ᵁU)→+*Y.functionField:=e.inv.hom.comp (X.germToFunctionField (f⁻¹ᵁU)).hom
  have hj:Function.Injective j:=
    (ConcreteCategory.bijective_of_isIso e.inv).injective.comp (X.germToFunctionField_injective (f⁻¹ᵁU))
  have hs:j.comp (f.app U).hom=algebraMap Γ(Y,U) Y.functionField:=by
    have he:=DominantFunctionField318.map_germ f U
    have hc: f.app U≫X.germToFunctionField (f⁻¹ᵁU)≫e.inv=Y.germToFunctionField U:=by
      rw [←Category.assoc,←he]
      simp [e]
    exact congrArg CommRingCat.Hom.hom hc
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (IntegralFractionComparison318.bijective (f.app U).hom (f.isIntegral_app U hU) j hj hs)

theorem restrict_isIso (U:Y.Opens) (hU:IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(Y,U)]:IsIso (f∣_U):=by
  exact (isIso_morphismRestrict_iff_isIso_app f hU).mpr (app_isIso f U hU)
end IntegralGenericIso318
