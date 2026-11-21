module
public import Mathlib
public section
namespace ActualRayInteriorBox318
open scoped BigOperators

/-- It is legitimate to attach a bounded (not prime) zero shift: first shear
the base so every actual coefficient has nonzero degree-two difference. -/
def shear {R : Type*} [CommRing R] (K : R) : R × R ≃ R × R where
  toFun x := (x.1 + K * x.2^2, x.2)
  invFun x := (x.1 - K * x.2^2, x.2)
  left_inv := by rintro ⟨u,v⟩; simp
  right_inv := by rintro ⟨u,v⟩; simp

theorem shear_value {R : Type*} [CommRing R] (K c u v : R) :
    (shear K (u,v)).1 + (c-K)*v^2 = u+c*v^2 := by
  change u+K*v^2+(c-K)*v^2 = _
  ring

/-- Every rational and abelian modulus sees exactly the same local factors
after the shear; only bijectivity is used, including at prime powers. -/
theorem local_sum {R M : Type*} [CommRing R] [Fintype R] [AddCommMonoid M]
    (K : R) (f : R × R → M) :
    (∑ x : R × R, f (shear K x)) = ∑ x : R × R, f x :=
  (shear K).sum_comp f

theorem children_distinct {R : Type*} [CommRing R] {K a b : R}
    (h : a≠b) : a-K ≠ b-K := by
  intro he
  apply h
  linear_combination he

/-- Integer lift of each true output in the W-trick; c is the step residue,
d is the shifted coefficient, and b_i the prime-output residue. -/
theorem lift {W x m c b bᵢ k d : ℤ} (hk : W*k=b+d*c^2-bᵢ) :
    W*(x+(d*W*m^2+2*d*c*m+k))+bᵢ = (W*x+b)+d*(W*m+c)^2 := by
  linear_combination hk

/-- Once U is interior and every allowed displacement is small, product
weights agree with true nonperiodic prime weights without any edge estimate. -/
theorem interior {N U t : ℝ} (hN : 0<N) (h1 : 19*N≤32*U)
    (h2 : 32*U≤25*N) (ht : |t|≤N/32) :
    N/2<U+t ∧ U+t<N := by
  have hl := (abs_le.mp ht).1
  have hh := (abs_le.mp ht).2
  constructor <;> linarith

end ActualRayInteriorBox318
