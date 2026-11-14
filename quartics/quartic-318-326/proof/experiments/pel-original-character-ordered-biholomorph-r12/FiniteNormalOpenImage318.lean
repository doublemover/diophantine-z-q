module
public import NormalFiniteImageDetection318
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FiniteNormalOpenImage318
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f:X⟶Y) [IsFinite f] [IsDominant f]
  (U:Y.Opens) [Nonempty U] [Nonempty (f⁻¹ᵁU)]

@[expose,instance_reducible] def sectionAlgebra:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
@[expose,instance_reducible] def nativeAlgebra:Algebra Γ(Y,U) X.functionField:=
  ((DominantFunctionField318.map f).hom.comp (Y.germToFunctionField U).hom).toAlgebra

/-- Actual section germs, with scalar compatibility supplied by the
naturality square of the SAME global generic-stalk pullback. -/
@[expose] def sectionGerm:
    letI:=sectionAlgebra f U
    letI:=nativeAlgebra f U
    Γ(X,f⁻¹ᵁU)→ₐ[Γ(Y,U)]X.functionField:=by
  letI:=sectionAlgebra f U
  letI:=nativeAlgebra f U
  exact {
    __:=(X.germToFunctionField (f⁻¹ᵁU)).hom
    commutes':=fun r=>(congrArg (fun h:Γ(Y,U)⟶X.functionField=>h r)
      (DominantFunctionField318.map_germ f U)).symm }
@[expose] def fieldMap:
    letI:=nativeAlgebra f U
    Y.functionField→ₐ[Γ(Y,U)]X.functionField:=by
  letI:=nativeAlgebra f U
  exact { __:=(DominantFunctionField318.map f).hom, commutes':=fun _=>rfl }

/-- On the FULL inverse image of any nonempty normal affine target open,
regular functions descend iff their actual generic germs are in the
actual native pullback image. No smaller source chart is substituted. -/
theorem range_iff (hU:IsAffineOpen U) [IsIntegrallyClosed Γ(Y,U)]
    (x:Γ(X,f⁻¹ᵁU)):
    x∈Set.range (f.app U).hom ↔
      X.germToFunctionField (f⁻¹ᵁU) x∈Set.range (DominantFunctionField318.map f).hom:=by
  letI:=sectionAlgebra f U
  letI:=nativeAlgebra f U
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=
    RingHom.finite_algebraMap.mp (f.finite_app U hU)
  letI:IsFractionRing Γ(Y,U) Y.functionField:=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  exact NormalFiniteImageDetection318.range_iff (sectionGerm f U) (fieldMap f U)
    (X.germToFunctionField_injective (f⁻¹ᵁU))
    (DominantFunctionField318.map f).hom.injective x

/-- Pullback of regular sections is injective for the actual dominant
map, with no assumption that the open omits ramification points. -/
theorem app_injective:Function.Injective (f.app U).hom:=by
  intro a b h
  apply Y.germToFunctionField_injective U
  apply (DominantFunctionField318.map f).hom.injective
  have ha:=congrArg (fun k:Γ(Y,U)⟶X.functionField=>k a)
    (DominantFunctionField318.map_germ f U)
  have hb:=congrArg (fun k:Γ(Y,U)⟶X.functionField=>k b)
    (DominantFunctionField318.map_germ f U)
  exact ha.trans ((congrArg (X.germToFunctionField (f⁻¹ᵁU)) h).trans hb.symm)
end FiniteNormalOpenImage318
