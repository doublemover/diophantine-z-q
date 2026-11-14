module
public import PELOriginalOrderKernelScheme318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public section
noncomputable section
namespace PELOriginalOrderLatticeMatrix318
open PELPrincipalOrderCoordinates318 PELOriginalOrderIntegralNorm318
/-- Left multiplication on the EXACT integral order basis. Rows retain
all half-integral basis corrections, not a rationally rescaled lattice. -/
@[expose] def matrix (a : order) : Matrix (Fin 4) (Fin 4) ℤ :=
  let x := coordinatesEquiv.symm a
  !![x 0,-210*x 1-126*x 3,x 2,-84*x 1-42*x 3;
     x 1,x 0+3*x 2,-2*x 1-x 3,x 2;
     x 2,42*x 3,x 0+x 2,-42*x 1;
     x 3,-5*x 2,5*x 1+3*x 3,x 0-2*x 2]
@[expose] def action (a : order) : Coordinates →ₗ[ℤ] Coordinates := Matrix.toLin' (matrix a)
lemma action_coordinates (a : order) (y : Coordinates) :
    coordinatesEquiv (action a y)=a*coordinatesEquiv y := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  have he : action (coordinatesEquiv x) y=product x y := by
    ext i
    fin_cases i <;>
      simp [action,matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,product] <;> ring
  rw [he]
  apply Subtype.ext
  exact embed_mul x y
lemma determinant (a : order) : (matrix a).det=(norm a)^2 := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  simp only [matrix,norm,AddEquiv.symm_apply_apply]
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three,Matrix.submatrix_apply,Fin.sum_univ_succ,
    Fin.succAbove, normCoordinates]
  <;> ring
lemma action_injective (a : order) (ha : norm a≠0) : Function.Injective (action a) := by
  intro x y h
  have hc : a*coordinatesEquiv x=a*coordinatesEquiv y := by
    rw [←action_coordinates,←action_coordinates,h]
  have hn := congrArg (fun t : order => conjugate a*t) hc
  simp only [←mul_assoc,conjugate_mul] at hn
  apply coordinatesEquiv.injective
  apply Subtype.ext
  have hq : (norm a:ℚ)≠0 := by exact_mod_cast ha
  -- The central nonzero rational scalar is invertible in the quaternion algebra.
  have hi : IsUnit (norm a:PELQuaternionAlgebra318.B) := by
    have he := (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ PELQuaternionAlgebra318.B)
    simpa only [map_intCast] using he
  obtain ⟨u,hu⟩ := hi
  have hv := congrArg Subtype.val hn
  change (norm a:PELQuaternionAlgebra318.B)*(coordinatesEquiv x:PELQuaternionAlgebra318.B)=
    (norm a:PELQuaternionAlgebra318.B)*(coordinatesEquiv y:PELQuaternionAlgebra318.B) at hv
  rw [←hu] at hv
  have he := congrArg (fun z : PELQuaternionAlgebra318.B => (↑(u⁻¹):PELQuaternionAlgebra318.B)*z) hv
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using he
end PELOriginalOrderLatticeMatrix318
