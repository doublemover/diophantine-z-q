module
public import PELSquareNormNormalizerKernel318
public section
noncomputable section
namespace PELNormalizerQuadraticCertificates318
open PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318
open scoped BigOperators
set_option maxHeartbeats 2000000

@[expose] def conjugateCoordinates (a : Coordinates) : Coordinates := ![a 0+a 2,-a 1,-a 2,-a 3]
@[expose] def row (k : Fin 16) : Fin 4 := ⟨k.val/4,by have h:=k.isLt; omega⟩
@[expose] def col (k : Fin 16) : Fin 4 := ⟨k.val%4,Nat.mod_lt _ (by decide)⟩
/-- The literal integer coordinate numerators of a*b_j*bar(a), before
normalizer integrality divides them by the ORIGINAL reduced norm. -/
@[expose] def numerator (a : Coordinates) (k : Fin 16) : ℤ :=
  product (product a (basis (row k))) (conjugateCoordinates a) (col k)

@[expose] def pairIndex : Fin 4 → Fin 4 → Fin 10 :=
  ![![0,1,2,3],![1,4,5,6],![2,5,7,8],![3,6,8,9]]
@[expose] def coefficient : Fin 10 → Fin 16 → ℤ :=
  ![![84,0,0,0,0,-42,0,-42,-84,0,0,0,0,210,0,168],
    ![0,0,0,0,-1,0,0,0,0,-84,0,-42,5,0,0,0],
    ![42,0,0,0,0,84,0,42,-42,0,0,0,0,-210,0,-126],
    ![0,0,0,0,0,0,0,0,0,210,0,126,-5,0,0,0],
    ![0,0,0,0,0,-1,0,0,-2,0,0,0,0,5,0,1],
    ![0,0,0,0,2,0,0,0,0,-42,0,0,-5,0,0,0],
    ![0,0,0,0,0,0,0,-1,5,0,0,0,0,-5,0,0],
    ![-84,0,0,0,0,42,0,0,84,0,0,0,0,0,0,42],
    ![0,0,0,0,-5,0,0,0,0,0,0,-42,10,0,0,0],
    ![0,0,0,0,0,5,0,5,-10,0,0,0,0,0,0,-5]]

/-- Exact integer certificates recover210 times EVERY quadratic monomial
from the16 actual conjugation numerators. Smith/Hermite ranks are not a premise. -/
theorem certificate (a : Coordinates) (i j : Fin 4) :
    210*a i*a j=∑ k : Fin 16,coefficient (pairIndex i j) k*numerator a k := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ,coefficient,pairIndex,numerator,row,col,product,basis,
      conjugateCoordinates,Pi.single_apply]
  all_goals ring

theorem monomial_divisibility (a : Coordinates) (N : ℤ)
    (hN : ∀ k : Fin 16,N∣numerator a k) (i j : Fin 4) : N∣210*a i*a j := by
  rw [certificate]
  apply Finset.dvd_sum
  intro k hk
  exact dvd_mul_of_dvd_right (hN k) _

/-- The integer Bezout identity is retained explicitly. Every primitive
coordinate is used, so no chosen nonzero coordinate or prime is omitted. -/
theorem primitive_norm_divides210 (a z : Coordinates) (N : ℤ)
    (hprimitive : ∑ i : Fin 4,z i*a i=1) (hN : ∀ k : Fin 16,N∣numerator a k) : N∣210 := by
  have he : 210*(∑ i : Fin 4,z i*a i)^2=
      ∑ i : Fin 4,∑ j : Fin 4,(z i*z j)*(210*a i*a j) := by
    simp only [Fin.sum_univ_succ]
    ring
  have hd : N∣∑ i : Fin 4,∑ j : Fin 4,(z i*z j)*(210*a i*a j) := by
    apply Finset.dvd_sum
    intro i hi
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_right (monomial_divisibility a N hN i j) _
  rw [←he,hprimitive] at hd
  norm_num at hd
  exact hd
end PELNormalizerQuadraticCertificates318
