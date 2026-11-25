module
public import SourceTwistArithmetic318

@[expose] public section
noncomputable section

namespace OriginalRationalCoarseTwists318
open SourceTwistArithmetic318
open scoped BigOperators

private theorem cubicA_ne (i : Fin 4) : cubicA i ≠ 0 := by
  fin_cases i <;> norm_num [cubicA]
private theorem cubicB_ne (i : Fin 4) : cubicB i ≠ 0 := by
  fin_cases i <;> norm_num [cubicB]
private theorem jacobianTwist_ne (i : Fin 4) : jacobianTwist i ≠ 0 := by
  fin_cases i <;> norm_num [jacobianTwist]

/-- Two actual short-Weierstrass coefficient equalities of a Q-isomorphism
recover the rational twist class; equality of j alone is insufficient.
The A- and B-coordinates together forbid an invisible sign change. -/
theorem complement_twist (i : Fin 4) (D s : ℚ) (hs : s ≠ 0)
    (a : publishedA i = s^4*D^2*cubicA i)
    (b : publishedB i = s^6*D^3*cubicB i) :
    D = twistClasses i * (twistSquare i/s)^2 := by
  have ha₀ : jacobianTwist i ^ 2 * cubicA i = (s^2*D)^2 * cubicA i := by
    calc
      _ = publishedA i := (published_twist_exact i).1.symm
      _ = s^4*D^2*cubicA i := a
      _ = _ := by ring
  have hb₀ : jacobianTwist i ^ 3 * cubicB i = (s^2*D)^3 * cubicB i := by
    calc
      _ = publishedB i := (published_twist_exact i).2.symm
      _ = s^6*D^3*cubicB i := b
      _ = _ := by ring
  have ha := mul_right_cancel₀ (cubicA_ne i) ha₀
  have hb := mul_right_cancel₀ (cubicB_ne i) hb₀
  have H : jacobianTwist i = s^2*D := by
    apply mul_right_cancel₀ (pow_ne_zero 2 (jacobianTwist_ne i))
    calc
      _ = jacobianTwist i ^ 3 := by ring
      _ = (s^2*D)^3 := hb
      _ = (s^2*D)*(s^2*D)^2 := by ring
      _ = _ := by rw [←ha]
  apply mul_left_cancel₀ (pow_ne_zero 2 hs)
  calc
    _ = jacobianTwist i := H.symm
    _ = twistClasses i * twistSquare i ^ 2 := jacobian_twist_class i
    _ = twistClasses i * (s * (twistSquare i/s))^2 := by
      have e : s * (twistSquare i/s) = twistSquare i := by
        rw [mul_comm,div_mul_cancel₀ _ hs]
      exact congrArg (fun w : ℚ => twistClasses i * w^2) e.symm
    _ = s^2 * (twistClasses i * (twistSquare i/s)^2) := by ring

abbrev comProduct (d : Fin 4→ℚ) (i : Fin 4) : ℚ :=
  ∏ j : Fin 3, d (complement i j)

private theorem complement_twice (d : Fin 4→ℚ) (i : Fin 4) :
    comProduct (comProduct d) i = d i * (∏ j : Fin 4, d j)^2 := by
  fin_cases i <;> norm_num [comProduct,complement,Fin.prod_univ_succ] <;> ring

/-- Invert the four complementary character twist identities before
choosing any square root. The exact rational square factors are constructed. -/
theorem reconstruct (d r : Fin 4→ℚ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i, comProduct d i = twistClasses i * (r i)^2) (i : Fin 4) :
    d i = constants i * (comProduct r i / (∏ j : Fin 4, d j))^2 := by
  have hp : (∏ j : Fin 4, d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _=>hd k)
  have e : comProduct (comProduct d) i = constants i * (comProduct r i)^2 := by
    unfold comProduct
    simp only [h,Finset.prod_mul_distrib,Finset.prod_pow]
    rw [source_constant_squareclasses]
  apply mul_right_cancel₀ (pow_ne_zero 2 hp)
  calc
    _ = comProduct (comProduct d) i := (complement_twice d i).symm
    _ = constants i * (comProduct r i)^2 := e
    _ = _ := by rw [mul_assoc,←mul_pow,div_mul_cancel₀ _ hp]

/-- Exact recognition of the four rational character squareclasses
when the true four named genus-one quotient Jacobian arrows supply
their actual short model scales. -/
theorem recover (d s : Fin 4→ℚ) (hd : ∀ i, d i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (a : ∀ i, publishedA i = (s i)^4*(comProduct d i)^2*cubicA i)
    (b : ∀ i, publishedB i = (s i)^6*(comProduct d i)^3*cubicB i) (i : Fin 4) :
    d i = constants i *
      (comProduct (fun k=>twistSquare k/s k) i / (∏ j : Fin 4, d j))^2 :=
  reconstruct d (fun k=>twistSquare k/s k) hd
    (fun k=>complement_twist k (comProduct d k) (s k) (hs k) (a k) (b k)) i

end OriginalRationalCoarseTwists318

#print axioms OriginalRationalCoarseTwists318.complement_twist
#print axioms OriginalRationalCoarseTwists318.reconstruct
#print axioms OriginalRationalCoarseTwists318.recover
