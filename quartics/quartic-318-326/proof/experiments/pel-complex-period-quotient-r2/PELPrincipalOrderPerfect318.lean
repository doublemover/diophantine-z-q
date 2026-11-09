module
public import PELPrincipalOrderCoordinates318
public section
noncomputable section
namespace PELPrincipalOrderPerfect318
open PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1000000
@[expose] def basis (i : Fin 4) : Coordinates := Pi.single i 1

theorem decompose (x : Coordinates) :
    x=x 0 • basis 0+x 1 • basis 1+x 2 • basis 2+x 3 • basis 3 := by
  ext i
  fin_cases i <;> simp [basis,Pi.single_apply]

theorem functional_value (f : Coordinates →ₗ[ℤ] ℤ) (y : Coordinates) :
    f y=y 0*f (basis 0)+y 1*f (basis 1)+y 2*f (basis 2)+y 3*f (basis 3) := by
  calc
    f y=f (y 0 • basis 0+y 1 • basis 1+y 2 • basis 2+y 3 • basis 3) :=
      congrArg f (decompose y)
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul]

/-- The inverse to the pairing-to-integral-dual map is explicit, including
the exact cross terms forced by the half-integral quaternion basis. -/
@[expose] def dualVector (f : Coordinates →ₗ[ℤ] ℤ) : Coordinates :=
  ![-f (basis 3),f (basis 2),2*f (basis 3)-f (basis 1),f (basis 0)-2*f (basis 2)]

theorem dualVector_value (f : Coordinates →ₗ[ℤ] ℤ) (y : Coordinates) :
    integralForm (dualVector f) y=f y := by
  rw [functional_value]
  simp [integralForm,dualVector]
  ring

theorem separating (x y : Coordinates)
    (h : ∀ z : Coordinates,integralForm x z=integralForm y z) : x=y := by
  have h0 := h (basis 0)
  have h1 := h (basis 1)
  have h2 := h (basis 2)
  have h3 := h (basis 3)
  norm_num [integralForm,basis,Pi.single_apply] at h0 h1 h2 h3
  ext i
  fin_cases i <;> omega

/-- Perfectness on the actual integral order coordinates: EVERY integral
linear functional is represented by a unique order element. No determinant
condition or principal-polarization hypothesis is supplied. -/
theorem perfect (f : Coordinates →ₗ[ℤ] ℤ) :
    ∃! x : Coordinates,∀ y : Coordinates,integralForm x y=f y := by
  refine ⟨dualVector f,dualVector_value f,?_⟩
  intro x hx
  apply separating
  intro y
  rw [hx,dualVector_value]

/-- Direct integral alternation, compatible with the unrescaled rational
trace pairing through pairing_value. -/
theorem alternating (x : Coordinates) : integralForm x x=0 := by
  unfold integralForm
  ring
end PELPrincipalOrderPerfect318
