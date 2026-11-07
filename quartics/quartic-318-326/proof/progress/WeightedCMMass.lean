module
public import Height13RealLog
public section
namespace WeightedCMMass

/-- The fixed integral denominator clearer in the literal source. -/
theorem denominator_clearer_value :
    (81-1 : ℤ)*(81-3)*(81-9)*(81-27)=24261120 ∧
    (24261120 : ℤ)=2^9*47385 ∧ (47385 : ℤ)%2=1 := by norm_num

/-- Each stabilizer has order two, each embedding orbit therefore has d
    elements when |R_z^×|=2d, and c0/(2d)=c is integral. Cancellation
    occurs in the integers, not in the coefficient residue field. -/
theorem orbit_mass (c0 c d : ℤ) (hc : c0=c*(2*d)) :
    c*d=c0/2 := by
  have h : c0=2*(c*d) := by rw [hc]; ring
  omega

/-- Counting the two moving-prime orientations together with the old-level
    orientations produces exactly c0*2^w, without a second factor two. -/
theorem total_mass (c0 c d : ℤ) (w : ℕ) (hc : c0=c*(2*d)) :
    2^(w+1)*(c*d)=c0*2^w := by rw [hc, pow_succ]; ring

variable {O : Type*} [CommRing O]

/-- Changing one chosen coefficient lift by 2^M retains full integer
    precision after the mass factor, since c is already integral. -/
theorem integral_lift_precision (c value err : O) (M : ℕ) :
    c*(value+2^M*err)-c*value=2^M*(c*err) := by ring

/-- Source O.7 after the actual geometric identification and sign count.
    Every orientation has the same phase-weighted class sum modulo 2^M;
    integral mass factors leave no precision loss. -/
theorem orientation_sum_precision {I : Type*} [Fintype I]
    (mass phase value : O) (err : I → O) (M w : ℕ)
    (hcard : Fintype.card I=2^(w+1)) (c0 : O)
    (hmass : 2*mass=c0) :
    (∑ i, mass*(phase*value+2^M*err i)) =
      c0*2^w*phase*value+2^M*(mass*∑ i,err i) := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  rw [pow_succ]
  calc
    _ = (2*mass)*2^w*phase*value+2^M*(mass*∑ i,err i) := by ring
    _ = _ := by rw [hmass]

/-- Both moving-prime orientation changes have sign minus one, hence the
    norm-weight and Schwartz-weight product is unchanged. -/
theorem double_sign (phase value : O) : (-phase)*(-value)=phase*value := by ring

#print axioms denominator_clearer_value
#print axioms orbit_mass
#print axioms total_mass
#print axioms integral_lift_precision
#print axioms orientation_sum_precision
#print axioms double_sign
end WeightedCMMass
