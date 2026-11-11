module
public import QuaternionicRealPeriod318
public import Mathlib.LinearAlgebra.Matrix.Notation
public section
noncomputable section
namespace QuaternionicMatrixCoordinates318
open QuaternionicRealPeriod318
set_option maxHeartbeats 1000000
abbrev Coordinates := Fin 4 → ℝ
variable (α β : ℝ)
@[expose] def split : Coordinates →ₗ[ℝ] RealMatrices where
  toFun v := !![v 0+β*v 2,-α*v 1+α*β*v 3;α*v 1+α*β*v 3,v 0-β*v 2]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r v := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
@[expose] def unsplit (M : RealMatrices) : Coordinates :=
  ![(M 0 0+M 1 1)/2,(M 1 0-M 0 1)/(2*α),
    (M 0 0-M 1 1)/(2*β),(M 0 1+M 1 0)/(2*α*β)]

theorem split_unsplit (hα : α≠0) (hβ : β≠0) (M : RealMatrices) :
    split α β (unsplit α β M)=M := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (M 0 0+M 1 1)/2+β*((M 0 0-M 1 1)/(2*β))=M 0 0
    field_simp [hβ] <;> ring
  · change -α*((M 1 0-M 0 1)/(2*α))+α*β*((M 0 1+M 1 0)/(2*α*β))=M 0 1
    field_simp [hα,hβ] <;> ring
  · change α*((M 1 0-M 0 1)/(2*α))+α*β*((M 0 1+M 1 0)/(2*α*β))=M 1 0
    field_simp [hα,hβ] <;> ring
  · change (M 0 0+M 1 1)/2-β*((M 0 0-M 1 1)/(2*β))=M 1 1
    field_simp [hβ] <;> ring

theorem unsplit_split (hα : α≠0) (hβ : β≠0) (v : Coordinates) :
    unsplit α β (split α β v)=v := by
  funext i
  fin_cases i
  · change ((v 0+β*v 2)+(v 0-β*v 2))/2=v 0
    ring
  · change ((α*v 1+α*β*v 3)-(-α*v 1+α*β*v 3))/(2*α)=v 1
    field_simp [hα] <;> ring
  · change ((v 0+β*v 2)-(v 0-β*v 2))/(2*β)=v 2
    field_simp [hβ] <;> ring
  · change ((-α*v 1+α*β*v 3)+(α*v 1+α*β*v 3))/(2*α*β)=v 3
    field_simp [hα,hβ] <;> ring

@[expose] def splitEquiv (hα : α≠0) (hβ : β≠0) : Coordinates ≃ₗ[ℝ] RealMatrices :=
  { split α β with
    invFun := unsplit α β
    left_inv := unsplit_split α β hα hβ
    right_inv := split_unsplit α β hα hβ }

/-- Coordinates in the exact ordered basis [1,i,(1+j)/2,i/2+k/10]. -/
@[expose] def orderCoordinates : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun v := ![v 0+v 2/2,v 1+v 3/2,v 2/2,v 3/10]
  invFun w := ![w 0-w 2,w 1-5*w 3,2*w 2,10*w 3]
  left_inv v := by funext i; fin_cases i <;> simp <;> ring
  right_inv w := by funext i; fin_cases i <;> simp <;> ring
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' r v := by funext i; fin_cases i <;> simp <;> ring

@[expose] def orderMatrixEquiv (hα : α≠0) (hβ : β≠0) : Coordinates ≃ₗ[ℝ] RealMatrices :=
  orderCoordinates.trans (splitEquiv α β hα hβ)

/-- The four actual order-basis periods are a full real basis for every
upper-half-plane parameter, not just four formal or rationally independent vectors. -/
@[expose] def orderPeriodEquiv (hα : α≠0) (hβ : β≠0) (τ : ℂ) (hτ : 0<τ.im) :
    Coordinates ≃ₗ[ℝ] ComplexVectors :=
  (orderMatrixEquiv α β hα hβ).trans (periodEquiv τ hτ)

@[expose] def periodBasis (hα : α≠0) (hβ : β≠0) (τ : ℂ) (hτ : 0<τ.im) :
    Module.Basis (Fin 4) ℝ ComplexVectors :=
  (Pi.basisFun ℝ (Fin 4)).map (orderPeriodEquiv α β hα hβ τ hτ)
end QuaternionicMatrixCoordinates318
