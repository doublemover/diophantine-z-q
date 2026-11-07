module
public import Height13RealLog
public import Mathlib.RingTheory.Coprime.Lemmas
public section
namespace ThetaRecurrence

/-- The integral/nonintegral partition cancels the removed divisible vectors.
No hypothesis that the phase is quadratic is used. -/
theorem neighbor_partition {R : Type*} [CommRing R]
    (t hp h hm k p s : R) :
    (t*hp-h)+((1+k)*h+p*s*hm) = t*hp+k*h+p*s*hm := by ring

/-- Moving the actual neighbor operator across the stack mass and multiplying
by its unit phase gives the two different phase powers in O.6. This holds in
any coefficient quotient ring, including O/(2^M), not only a field. -/
theorem weighted_recurrence {R : Type*} [CommRing R]
    (s t hp h hm k p chi a : R) (hst : s*t=1)
    (hneighbor : t*hp+k*h+p*s*hm=chi*a*h) :
    hp+s*k*h+p*s^2*hm=s*chi*a*h := by
  have he := congrArg (fun x : R => s*x) hneighbor
  calc
    hp+s*k*h+p*s^2*hm = (s*t)*hp+s*k*h+p*s^2*hm := by rw [hst]; ring
    _ = s*(t*hp+k*h+p*s*hm) := by ring
    _ = s*(chi*a*h) := he
    _ = s*chi*a*h := by ring

/-- Extraction H(mn) uses the Legendre factor mu=(m/p), while the
neighbor eigenvalue uses chi=chi_h*(p). Only chi, not s, is quadratic. -/
theorem extraction_phases {R : Type*} [CommRing R]
    (hp h hm s chi mu k p a : R) (hchi : chi^2=1)
    (hrec : hp+s*(mu*k)*h+p*s^2*hm=s*chi*a*h) :
    hp=((s*chi)*a-(s*mu)*k)*h-p*(s*chi)^2*hm := by
  have hsq : (s*chi)^2=s^2 := by rw [mul_pow, hchi, mul_one]
  rw [hsq]
  linear_combination hrec

/-- The actual isogeny/dual-isogeny count gives the reciprocal automorphism
mass, not the automorphism mass. -/
theorem mass_reciprocity (nij nji wi wj : ℚ) (hi : wi≠0) (hj : wj≠0)
    (hc : nij*wj=nji*wi) : nij/wi=nji/wj := by
  exact (div_eq_div_iff hi hj).mpr hc

/-- In the primitive nilpotent case y=[a,b;c,-a], the norm condition
forces the additional p in c; this is what makes y/p integral at the
unique kernel-line neighbor even when p divides the target index. -/
theorem primitive_neighbor_integrality (p a b c : ℤ)
    (ha : p ∣ a) (hb : IsCoprime p b)
    (hnorm : p^2 ∣ -a^2-b*c) : p^2 ∣ c := by
  have ha2 : p^2 ∣ a^2 := pow_dvd_pow_of_dvd ha 2
  have hbc : p^2 ∣ b*c := by
    have hh := dvd_sub (dvd_neg.mpr ha2) hnorm
    convert hh using 1; ring
  exact hb.pow_left.dvd_of_dvd_mul_left hbc

end ThetaRecurrence
#print axioms ThetaRecurrence.neighbor_partition
#print axioms ThetaRecurrence.weighted_recurrence
#print axioms ThetaRecurrence.extraction_phases
#print axioms ThetaRecurrence.mass_reciprocity
#print axioms ThetaRecurrence.primitive_neighbor_integrality
