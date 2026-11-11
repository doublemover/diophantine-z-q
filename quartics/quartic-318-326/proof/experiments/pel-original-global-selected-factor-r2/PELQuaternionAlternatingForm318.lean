module
public import PELQuaternionAlgebra318
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public section
noncomputable section
namespace PELQuaternionAlternatingForm318
open PELQuaternionAlgebra318 QuaternionAlgebra
set_option maxHeartbeats 1000000

/-- The literal trace pairing for the fixed μ, with no normalization by an
unproved polarization degree or choice of maximal-order basis. -/
@[expose] def pairing (x y : B) : ℚ := reducedTrace (muInverse*x*star y)

theorem coordinates (x y : B) : pairing x y=
    2*(x.imI*y.re-x.re*y.imI+5*x.imJ*y.imK-5*x.imK*y.imJ) := by
  simp [pairing,reducedTrace,muInverse]
  ring

theorem add_left (x x' y : B) : pairing (x+x') y=pairing x y+pairing x' y := by
  simp only [coordinates,QuaternionAlgebra.re_add,QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add,QuaternionAlgebra.imK_add]
  ring

theorem add_right (x y y' : B) : pairing x (y+y')=pairing x y+pairing x y' := by
  simp only [coordinates,QuaternionAlgebra.re_add,QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add,QuaternionAlgebra.imK_add]
  ring

theorem smul_left (r : ℚ) (x y : B) : pairing (r • x) y=r*pairing x y := by
  simp only [coordinates,QuaternionAlgebra.re_smul,QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul,QuaternionAlgebra.imK_smul,smul_eq_mul]
  ring

theorem smul_right (r : ℚ) (x y : B) : pairing x (r • y)=r*pairing x y := by
  simp only [coordinates,QuaternionAlgebra.re_smul,QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul,QuaternionAlgebra.imK_smul,smul_eq_mul]
  ring

@[expose] def form : LinearMap.BilinForm ℚ B where
  toFun x :=
    { toFun := pairing x
      map_add' := add_right x
      map_smul' := by intro r y; exact smul_right r x y }
  map_add' x x' := by ext y; exact add_left x x' y
  map_smul' r x := by ext y; exact smul_left r x y

theorem alternating (x : B) : pairing x x=0 := by rw [coordinates]; ring

theorem skew (x y : B) : pairing x y= -pairing y x := by rw [coordinates,coordinates]; ring

/-- The original LEFT quaternion action is adjoint to precisely the fixed
positive Rosati involution, with the same trace pairing on both sides. -/
theorem left_action_adjoint (a x y : B) : pairing (a*x) y=pairing x (rosati a*y) := by
  simp only [coordinates,rosati_coordinates]
  simp
  ring

/-- Nondegeneracy is explicit on the actual four-dimensional rational carrier.
This alone does not assert that its restriction to a maximal order is principal. -/
theorem nondegenerate (x : B) (hx : ∀ y : B,pairing x y=0) : x=0 := by
  have h0 := hx 1
  have h1 := hx mu
  have h2 := hx j
  have h3 := hx k
  rw [coordinates] at h0 h1 h2 h3
  norm_num [mu,j,k] at h0 h1 h2 h3
  ext <;> dsimp <;> linarith
end PELQuaternionAlternatingForm318
