module
public import ActualDetectorTrace318
public section
noncomputable section
namespace DetectorPrimeProduct318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318 ContactWeightWitness318
set_option maxHeartbeats 1000000

/-- Exact five contacts, including the two rational contacts of the current
source. No old determinant normalization is used. -/
@[expose] def theta : Fin 5 → ℚ := ![0,-1/2,-1,1/2399,-32/407]
@[expose] def linear (c u d : ℚ) (j : Fin 5) : ℚ := u-theta j*d^2/c^2
@[expose] def product (k : Fin 5 → ℤ) : ℤ := k 0*k 1*k 2*k 3*k 4
@[expose] def squareFactor (w : Assignment) (c u d : ℚ) : ℚ :=
  traceQuotient w c (u/d^2)/(d^5*(delta c (u/d^2))^3)

lemma product_cast (k : Fin 5 → ℤ) :
    (product k:ℚ)=(k 0:ℚ)*(k 1:ℚ)*(k 2:ℚ)*(k 3:ℚ)*(k 4:ℚ) := by
  simp only [product,Int.cast_mul]

lemma contact_product (c u d : ℚ) (hc : c≠0) (hd : d≠0) :
    contact (parameter c (u/d^2))=
      c^10/d^10*(linear c u d 0*linear c u d 1*linear c u d 2*
        linear c u d 3*linear c u d 4) := by
  norm_num [contact,parameter,linear,theta]
  field_simp [hc,hd] <;> ring

/-- The c^10 source normalization cancels the five c^2 factors. The exact
square denominator is d^5*delta^3, not a rescaled independent witness. -/
theorem pole_product (w : Assignment) (c u d : ℚ) (hc : c≠0) (hd : d≠0)
    (k : Fin 5 → ℤ) (hk : ∀ j, linear c u d j=(k j:ℚ)) :
    poleInput w c (u/d^2)=(product k:ℚ)*(squareFactor w c u d)^2 := by
  rw [poleInput,contact_product c u d hc hd,hk 0,hk 1,hk 2,hk 3,hk 4,←product_cast]
  by_cases hdelta : delta c (u/d^2)=0
  · simp [squareFactor,hdelta]
  · unfold squareFactor
    field_simp [hc,hd,hdelta] <;> ring

lemma product_ne (k : Fin 5 → ℤ) (hk : ∀ j, k j≠0) : product k≠0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hk 0) (hk 1)) (hk 2)) (hk 3)) (hk 4)

lemma product_positive (k : Fin 5 → ℤ) (hk : ∀ j, 0<k j) : 0<product k :=
  mul_pos (mul_pos (mul_pos (mul_pos (hk 0) (hk 1)) (hk 2)) (hk 3)) (hk 4)

/-- Local square inputs concern precisely the five selected integer values.
The squareclass transport is valid in every characteristic-zero field. -/
theorem pole_local_square {F : Type*} [Field F] [CharZero F]
    (w : Assignment) (c u d : ℚ) (hc : c≠0) (hd : d≠0)
    (k : Fin 5 → ℤ) (hk : ∀ j, linear c u d j=(k j:ℚ))
    (hs : ∀ j, IsSquare (k j:F)) : IsSquare (poleInput w c (u/d^2):F) := by
  rw [pole_product w c u d hc hd k hk,Rat.cast_mul,Rat.cast_pow]
  have hp := ((((hs 0).mul (hs 1)).mul (hs 2)).mul (hs 3)).mul (hs 4)
  have hp' : IsSquare ((product k:ℚ):F) := by simpa [product] using hp
  exact hp'.mul ⟨(squareFactor w c u d:F),by ring⟩

end DetectorPrimeProduct318
