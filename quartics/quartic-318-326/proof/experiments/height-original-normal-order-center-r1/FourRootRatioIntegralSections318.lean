module
public import FourRootRatioDualTransport318
public section
noncomputable section
namespace FourRootRatioIntegralSections318
open FourRootRatioOrder318 FourRootRatioGenericEquiv318 FourRootRatioDualTransport318
open FourRootOrderSigns318 FourRootIntegralDuality318 FiniteDualTransport318
variable {R : Type*} [CommRing R] (h : Rˣ) (s c : R)
@[expose] def coefficient0 : R := c*(↑h⁻¹:R)^3*s
@[expose] def coefficient1 : R := c*(↑h⁻¹:R)^3

/-- Cancellation already holds IN the integral coefficient ring, before
any ramified coordinate is inverted. The unit is only the nonvanishing factor. -/
lemma coefficient0_identity : coefficient0 h s c*((h:R)*s)^3=c*s^4 := by
  unfold coefficient0
  calc
    _ = c*((↑h⁻¹:R)*(h:R))^3*s^4 := by ring
    _ = _ := by rw [Units.inv_mul,one_pow,mul_one]
lemma coefficient1_identity : coefficient1 h c*((h:R)*s)^3=c*s^3 := by
  unfold coefficient1
  calc
    _ = c*((↑h⁻¹:R)*(h:R))^3*s^3 := by ring
    _ = _ := by rw [Units.inv_mul,one_pow,mul_one]

variable (q : R) (r : Fin 3 → R) (hq : IsUnit q)
local notation "A" => OriginalOrder q r
local notation "B" => RatioOrder q r
local notation "E" => equiv q r hq

lemma forward_scaled (k : R) :
    squareTransport E (squareFrame (frame (original q r))
      (algebraMap R A k*generator (original q r) 0^6)) =
    squareFrame (frame (normalized q r)) (algebraMap R B k) := by
  rw [forward_square,←map_mul]
  rw [←rootUnit_value q r hq,mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one,AlgEquiv.commutes]

lemma root_sixth : generator (original q r) 0^6=algebraMap R A (q^3) := by
  rw [show (6:ℕ)=2*3 from rfl,pow_mul,generator_square,←map_pow]
  rfl

variable (he : q=(h:R)*s)
include he in
/-- The original S^4 section becomes the actual integral coefficient
c*h^-3*S in the normalized-order dual tensor square. -/
lemma section0_image :
    squareTransport E (squareFrame (frame (original q r)) (algebraMap R A (c*s^4))) =
    squareFrame (frame (normalized q r)) (algebraMap R B (coefficient0 h s c)) := by
  have hc : algebraMap R A (c*s^4)=
      algebraMap R A (coefficient0 h s c)*generator (original q r) 0^6 := by
    rw [root_sixth,←map_mul,he,coefficient0_identity]
  rw [hc]
  exact forward_scaled q r hq _

include he in
/-- The original S^3 section becomes c*h^-3, including its exact unit
factor. No unverified scalar proportionality is substituted. -/
lemma section1_image :
    squareTransport E (squareFrame (frame (original q r)) (algebraMap R A (c*s^3))) =
    squareFrame (frame (normalized q r)) (algebraMap R B (coefficient1 h c)) := by
  have hc : algebraMap R A (c*s^3)=
      algebraMap R A (coefficient1 h c)*generator (original q r) 0^6 := by
    rw [root_sixth,←map_mul,he,coefficient1_identity]
  rw [hc]
  exact forward_scaled q r hq _
end FourRootRatioIntegralSections318
