module
public import OpenJModel318
public import Mathlib.Algebra.Polynomial.Coeff
public section
noncomputable section

open Polynomial

namespace SelectedOriginalLiteralScalarUniqueness318

/-- The actual original localized coefficient map is uniquely fixed
by the image of the literal J. In particular the map to a common
generic coefficient field cannot depend on the choice of vertical
trait or on a unit witness for J−1728. -/
theorem over_original_j_eq {S : Type*} [CommRing S] (N : ℕ)
    (f g : OpenJModel318.Base N →+* S)
    (h : f (OpenJModel318.jCoord N) = g (OpenJModel318.jCoord N)) : f=g := by
  apply IsLocalization.ringHom_ext (.powers (OpenJModel318.denominator N))
  apply RingHom.ext
  intro p
  change f (algebraMap ℤ[X] (OpenJModel318.Base N) p) =
    g (algebraMap ℤ[X] (OpenJModel318.Base N) p)
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add,ha,hb]
  | monomial n a =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.C_eq_intCast]
    simpa only [map_mul,map_pow,map_intCast,←OpenJModel318.jCoord,h]

end SelectedOriginalLiteralScalarUniqueness318

#print axioms SelectedOriginalLiteralScalarUniqueness318.over_original_j_eq
