module
public import Height13RealLog
public section
namespace WholePrimeOmission
variable {k : Type*} [Field k] [CharP k 2]

/-- Reduction of O.12 followed by the two actual first-shell readings.
    The shared omitted coefficient is essential: this theorem does not
    allow changing source, depth, phase, or finite stage after omission. -/
theorem same_stage_omission (a0 a1 c0 c1 b0 b1 : k)
    (htrace : a1-a0 = c1*b1-c0*b0)
    (hsame : b1=b0) (hflip : c1+c0=1) : a1+a0=b0 := by
  simp only [sub_eq_add_neg, CharTwo.neg_eq] at htrace
  rw [hsame, ← add_mul, hflip, one_mul] at htrace
  exact htrace

/-- For arbitrary integer normalization exponent, work with its nonzero
    field scale z. This is the source first-shell coefficient identity. -/
theorem first_shell_factor {F : Type*} [Field F] [CharZero F]
    (eta C A z : F) (hz : z ≠ 0) (a kappa : F)
    (hC : a-kappa-1=2*C) :
    eta*((a-kappa)*A-A)/(4*z) = eta*C*(A/(2*z)) := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h2 : (2 : F) ≠ 0 := by norm_num
  rw [show (a-kappa)*A-A = (a-kappa-1)*A by ring, hC]
  field_simp
  ring

#print axioms same_stage_omission
#print axioms first_shell_factor
end WholePrimeOmission
