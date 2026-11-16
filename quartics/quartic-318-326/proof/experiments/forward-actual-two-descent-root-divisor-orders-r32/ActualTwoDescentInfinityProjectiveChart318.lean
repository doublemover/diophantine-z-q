module
public import ActualTwoDescentOriginalThetaPairingComparison318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section
namespace ActualTwoDescentInfinityProjectiveChart318
open ActualTwoDescentEllipticModel318
variable {K : Type*} [Field K] [CharZero K]

/-- Literal Y=1 chart of the original homogeneous cubic. -/
def infinityEquation (n u v : K) : Prop :=
  v-u^3-2*n*u^2*v+3*n^2*u*v^2=0

theorem actual_projective_infinity_chart (n u v : K) :
    (curve n).toProjective.Equation ![u,1,v] ↔ infinityEquation n u v := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [curve,WeierstrassCurve.Projective.fin3_def_ext,one_pow,zero_mul,
    mul_zero,zero_add,add_zero,mul_one,one_mul,infinityEquation]
  constructor <;> intro h <;> linear_combination h

/-- O is an actual smooth point of the original projective curve, even
without n nonzero. The derivative in the v direction is one there. -/
lemma actual_projective_infinity_smooth (n : K) :
    (curve n).toProjective.Nonsingular ![0,1,0] := by
  rw [WeierstrassCurve.Projective.nonsingular_iff]
  refine ⟨WeierstrassCurve.Projective.equation_zero,?_⟩
  simp [curve,WeierstrassCurve.Projective.fin3_def_ext]

/-- Exact overlap with the original affine chart, not a different model. -/
theorem actual_infinity_affine_overlap (n u v : K) (hv : v ≠ 0) :
    infinityEquation n u v ↔ (1/v)^2=(u/v)*(u/v-n)*(u/v+3*n) := by
  unfold infinityEquation
  constructor
  · intro h
    field_simp [hv]
    linear_combination h
  · intro h
    field_simp [hv] at h
    linear_combination h

lemma actual_affine_infinity_coordinates (n x y : K) (hy : y ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) : infinityEquation n (x/y) (1/y) := by
  unfold infinityEquation
  field_simp [hy]
  linear_combination hc

end ActualTwoDescentInfinityProjectiveChart318
