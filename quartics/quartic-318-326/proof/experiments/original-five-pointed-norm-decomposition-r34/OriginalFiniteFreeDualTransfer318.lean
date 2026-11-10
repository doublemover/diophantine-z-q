module
public import OriginalDualAlgebraNormTrace318
public import FiniteFreeGenericTransfer318
public import OpenDominantTrace318
public import OpenDominantNorm318
public section
noncomputable section
namespace OriginalFiniteFreeDualTransfer318
open AlgebraicGeometry CategoryTheory
open TrivSqZeroExt
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
local instance sectionAlgebra : Algebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
local instance dualSectionAlgebra : Algebra (DualNumber Γ(Y,U)) (DualNumber Γ(X,f ⁻¹ᵁ U)) :=
  OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
include hU in
lemma trace_eq (bs : Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U)) (s : Γ(X,f ⁻¹ᵁ U)) :
    Algebra.trace Γ(Y,U) Γ(X,f ⁻¹ᵁ U) s = OpenDominantTrace318.trace f hY hfinite U s := by
  letI : Nonempty (f ⁻¹ᵁ U) := DominantFunctionField318.preimage_nonempty f U
  rw [Algebra.trace_eq_matrix_trace bs]
  apply Y.germToFunctionField_injective U
  exact (FiniteFreeGenericTransfer318.trace_germ f U hU bs s).trans
    (OpenDominantTrace318.trace_embedding f hY hfinite U s).symm
include hU in
lemma norm_eq (bs : Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U)) (s : Γ(X,f ⁻¹ᵁ U)) :
    Algebra.norm Γ(Y,U) s = OpenDominantNorm318.norm f hY U s := by
  letI : Nonempty (f ⁻¹ᵁ U) := DominantFunctionField318.preimage_nonempty f U
  rw [Algebra.norm_eq_matrix_det bs]
  apply Y.germToFunctionField_injective U
  exact (FiniteFreeGenericTransfer318.norm_germ f U hU bs s).trans
    (OpenDominantNorm318.norm_embedding f hY U s).symm
include hU in
/-- On the original entire finite-free section ring, the dual determinant norm
extends the OLD regular norm, identified through the unchanged generic germ. -/
lemma norm_coefficient (bs : Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U)) (s : Γ(X,f ⁻¹ᵁ U)) :
    Algebra.norm (DualNumber Γ(Y,U)) (inl s : DualNumber Γ(X,f ⁻¹ᵁ U)) =
      inl (OpenDominantNorm318.norm f hY U s) := by
  letI := Module.Free.of_basis bs
  letI := Module.Finite.of_basis bs
  rw [OriginalDualAlgebraNormTrace318.norm_inl, norm_eq f hY U hU bs]
include hU in
/-- The same original finite-free dual determinant norm has the OLD actual
all-open regular trace as its first-order unit coefficient. This identifies
the original transfer, not a newly declared abstract tangent map. -/
lemma norm_unit (bs : Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U)) (s : Γ(X,f ⁻¹ᵁ U)) :
    Units.map (Algebra.norm (DualNumber Γ(Y,U))) (SquareZeroUnit318.unit Γ(X,f ⁻¹ᵁ U) s) =
      SquareZeroUnit318.unit Γ(Y,U) (OpenDominantTrace318.trace f hY hfinite U s) := by
  letI := Module.Free.of_basis bs
  letI := Module.Finite.of_basis bs
  rw [OriginalDualAlgebraNormTrace318.norm_unit, trace_eq f hY hfinite U hU bs]
end OriginalFiniteFreeDualTransfer318
