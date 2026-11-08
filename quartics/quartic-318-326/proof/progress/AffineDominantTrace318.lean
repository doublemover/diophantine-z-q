module
public import IntegralFieldTrace318
public import AffineDominantNorm318
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace AffineDominantTrace318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (U:Y.Opens) (hU:IsAffineOpen U)
    [Nonempty U] [IsIntegrallyClosed Γ(Y,U)]
variable (hfinite:letI:=AffineDominantNorm318.fieldAlgebra f
  FiniteDimensional Y.functionField X.functionField)
/-- Additive regular trace on the actual whole section ring over a normal
affine target open, with its actual app and generic pullback maps. -/
@[expose] def trace:Γ(X,f⁻¹ᵁU)→+Γ(Y,U):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:FiniteDimensional Y.functionField X.functionField:=hfinite
  letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=f.finite_app U hU
  exact (IntegralFieldTrace318.trace Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField).toAddMonoidHom
lemma embedding (x:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (trace f U hU hfinite x)=
      Algebra.trace Y.functionField X.functionField (X.germToFunctionField (f⁻¹ᵁU) x):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:FiniteDimensional Y.functionField X.functionField:=hfinite
  letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=f.finite_app U hU
  exact IntegralFieldTrace318.trace_embedding Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField x
lemma pullback (x:Γ(Y,U)):
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    trace f U hU hfinite (f.app U x)=Module.finrank Y.functionField X.functionField • x:=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:FiniteDimensional Y.functionField X.functionField:=hfinite
  letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=f.finite_app U hU
  exact IntegralFieldTrace318.trace_algebraMap Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField x
lemma linearity (a:Γ(Y,U)) (x:Γ(X,f⁻¹ᵁU)):
    trace f U hU hfinite (f.app U a*x)=a*trace f U hU hfinite x:=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:FiniteDimensional Y.functionField X.functionField:=hfinite
  letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=f.finite_app U hU
  exact (IntegralFieldTrace318.trace Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField).map_smul a x
end AffineDominantTrace318
