module
public import IntegralFieldNorm318
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace AffineDominantNorm318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (U:Y.Opens) (hU:IsAffineOpen U)
    [Nonempty U] [IsIntegrallyClosed Γ(Y,U)]
@[expose,instance_reducible] def fieldAlgebra:Algebra Y.functionField X.functionField:=
  (DominantFunctionField318.map f).hom.toAlgebra
/-- Norm on the actual entire section ring over a normal affine open. -/
@[expose] def norm:Γ(X,f⁻¹ᵁU)→*Γ(Y,U):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
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
  exact IntegralFieldNorm318.norm Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField
lemma embedding (x:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
    Y.germToFunctionField U (norm f U hU x)=
      Algebra.norm Y.functionField (X.germToFunctionField (f⁻¹ᵁU) x):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
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
  exact IntegralFieldNorm318.norm_embedding Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField x
lemma pullback (x:Γ(Y,U)):
    letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
    norm f U hU (f.app U x)=x^Module.finrank Y.functionField X.functionField:=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
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
  exact IntegralFieldNorm318.norm_algebraMap Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField x
lemma unique (n:Γ(X,f⁻¹ᵁU)→*Γ(Y,U))
    (hn:letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
        letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
        ∀x,Y.germToFunctionField U (n x)=
          Algebra.norm Y.functionField (X.germToFunctionField (f⁻¹ᵁU) x)):
    n=norm f U hU:=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=fieldAlgebra f
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
  exact IntegralFieldNorm318.unique Γ(Y,U) Γ(X,f⁻¹ᵁU) Y.functionField X.functionField n hn
end AffineDominantNorm318
