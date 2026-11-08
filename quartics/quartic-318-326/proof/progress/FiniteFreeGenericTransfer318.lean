module
public import AffinePrincipalBasis318
public import AffineDominantNorm318
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Algebraic.Integral
public section
noncomputable section
namespace FiniteFreeGenericTransfer318
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (U:Y.Opens) (hU:IsAffineOpen U) [Nonempty U]
local instance preimageNE:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
local instance sectionAlgebra:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
include hU in
lemma faithful:FaithfulSMul Γ(Y,U) Γ(X,f⁻¹ᵁU):=by
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:IsFractionRing Γ(X,f⁻¹ᵁU) X.functionField:=
    functionField_isFractionRing_of_isAffineOpen X (f⁻¹ᵁU) (hU.preimage f)
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro a b h
  apply IsFractionRing.injective Γ(Y,U) Y.functionField
  apply (algebraMap Y.functionField X.functionField).injective
  simpa only [←IsScalarTower.algebraMap_apply] using congrArg (algebraMap Γ(X,f⁻¹ᵁU) X.functionField) h
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
include hU
/-- The trace of the actual multiplication matrix has the original field
trace as its actual generic germ, with both literal scalar towers. -/
lemma trace_germ (bs:Module.Basis ι Γ(Y,U) Γ(X,f⁻¹ᵁU)) (s:Γ(X,f⁻¹ᵁU)):
    letI:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (Matrix.trace (Algebra.leftMulMatrix bs s))=
      Algebra.trace Y.functionField X.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=by
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:IsFractionRing Γ(X,f⁻¹ᵁU) X.functionField:=
    functionField_isFractionRing_of_isAffineOpen X (f⁻¹ᵁU) (hU.preimage f)
  letI:Module.Free Γ(Y,U) Γ(X,f⁻¹ᵁU):=Module.Free.of_basis bs
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=Module.Finite.of_basis bs
  letI:FaithfulSMul Γ(Y,U) Γ(X,f⁻¹ᵁU):=faithful f U hU
  rw [←Algebra.trace_eq_matrix_trace bs]
  exact (Algebra.trace_localization Γ(Y,U) (nonZeroDivisors Γ(Y,U)) s).symm
/-- The det of the actual multiplication matrix has the original field
norm as its actual generic germ, with both literal scalar towers. -/
lemma norm_germ (bs:Module.Basis ι Γ(Y,U) Γ(X,f⁻¹ᵁU)) (s:Γ(X,f⁻¹ᵁU)):
    letI:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (Matrix.det (Algebra.leftMulMatrix bs s))=
      Algebra.norm Y.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=by
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  letI:Algebra Γ(Y,U) X.functionField:=
    ((algebraMap Y.functionField X.functionField).comp (algebraMap Γ(Y,U) Y.functionField)).toAlgebra
  letI:IsScalarTower Γ(Y,U) Y.functionField X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower Γ(Y,U) Γ(X,f⁻¹ᵁU) X.functionField:=
    IsScalarTower.of_algebraMap_eq (fun a=>congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a)
      (DominantFunctionField318.map_germ f U))
  letI:IsFractionRing Γ(Y,U) Y.functionField:=functionField_isFractionRing_of_isAffineOpen Y U hU
  letI:IsFractionRing Γ(X,f⁻¹ᵁU) X.functionField:=
    functionField_isFractionRing_of_isAffineOpen X (f⁻¹ᵁU) (hU.preimage f)
  letI:Module.Free Γ(Y,U) Γ(X,f⁻¹ᵁU):=Module.Free.of_basis bs
  letI:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=Module.Finite.of_basis bs
  letI:FaithfulSMul Γ(Y,U) Γ(X,f⁻¹ᵁU):=faithful f U hU
  rw [←Algebra.norm_eq_matrix_det bs]
  exact (Algebra.norm_localization Γ(Y,U) (nonZeroDivisors Γ(Y,U)) s).symm
end FiniteFreeGenericTransfer318
