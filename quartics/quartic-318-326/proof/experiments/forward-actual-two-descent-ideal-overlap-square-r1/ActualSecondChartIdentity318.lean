module
public import ActualGaussianChartObstruction318
public section
noncomputable section
namespace ActualSecondChartIdentity318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318
set_option maxHeartbeats 6000000

/-- The parameter in the NORM FACTORS shifts; the original source label
and its lattice modulus do NOT. K itself remains the actual source form. -/
theorem shifted_identity {F : Type*} [CommRing F] (κ t : F) (y : Vector F) :
    (t+2)^2*K κ t y-t^2*D (t+2) y=
      P' κ t y*(κ*(t+2)*y.2.2^2+2*t^3+8*t^2-2*t*y.1*y.2.1+8*t-2*y.1*y.2.1) := by
  dsimp [K,D,P']
  ring

lemma shifted_zero {F : Type*} [Field F] (κ t : F) (ht : t≠0) (y : Vector F)
    (hP : P' κ t y=0) (hK : K κ t y=0) : D (t+2) y=0 := by
  have hh := shifted_identity κ t y
  rw [hP,hK,zero_mul,mul_zero,zero_sub,neg_eq_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 ht)

/-- Converse is only valid when t+2 is NONZERO in the actual residue field.
Primes dividing t+2 are handled by the actual quartic, never dropped. -/
lemma shifted_zero_iff {F : Type*} [Field F] (κ t : F) (ht : t≠0) (ht2 : t+2≠0)
    (y : Vector F) (hP : P' κ t y=0) : K κ t y=0 ↔ D (t+2) y=0 := by
  refine ⟨shifted_zero κ t ht y hP,?_⟩
  intro hD
  have hh := shifted_identity κ t y
  rw [hP,hD,zero_mul,mul_zero,sub_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 ht2)

lemma exceptional_x {F : Type*} [CommRing F] (κ t z w : F) (ht2 : t+2=0) :
    K κ t (0,z,w)=κ^2*w^4+4*z^2 := by
  have ht : t=-2 := eq_neg_of_add_eq_zero_left ht2
  rw [ht]
  dsimp [K]
  ring
lemma exceptional_z {F : Type*} [CommRing F] (κ t x w : F) (ht2 : t+2=0) :
    K κ t (x,0,w)=κ^2*w^4+4*x^2 := by
  have ht : t=-2 := eq_neg_of_add_eq_zero_left ht2
  rw [ht]
  dsimp [K]
  ring

end ActualSecondChartIdentity318
