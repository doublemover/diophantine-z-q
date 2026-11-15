module
public import FiniteFiveAffineFiber318
public section
noncomputable section
namespace ActualOriginalModularLift318
open QuadricCRTAssembly318 ActualQuadricTaylor318
set_option maxHeartbeats 16000000

/-- Literal nonnegative base-p digit representatives, not a ring map
from the finite field back to the integers. -/
@[expose] def digits (p : ℕ) (h : Coordinates (ZMod p)) : Coordinates ℤ :=
  (((h.1.1.val:ℤ),(h.1.2.val:ℤ)),((h.2.1.1.val:ℤ),(h.2.1.2.val:ℤ)),(h.2.2.val:ℤ))
lemma digits_reduce (p : ℕ) [NeZero p] (h : Coordinates (ZMod p)) :
    mapCoordinates (Int.castRingHom (ZMod p)) (digits p h)=h := by
  simp only [mapCoordinates,digits,Int.castRingHom_apply,Int.cast_natCast,ZMod.natCast_zmod_val]

lemma derivative_reduce (κ : ℤ) (p : ℕ) [NeZero p] (x : Coordinates ℤ)
    (h : Coordinates (ZMod p)) :
    (derivative κ x (digits p h):ZMod p)=
      derivative (κ:ZMod p) (mapCoordinates (Int.castRingHom (ZMod p)) x) h := by
  simp only [derivative,digits,mapCoordinates,Int.castRingHom_apply,Int.cast_sub,Int.cast_add,
    Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,ZMod.natCast_zmod_val]

@[expose] def offset (κ : ℤ) (x : Coordinates ℤ) (m : ℤ) : ℤ := equation κ x/m
lemma actual_offset_identity (κ : ℤ) (x : Coordinates ℤ) (m : ℤ) (hx : m∣equation κ x) :
    equation κ x=m*offset κ x m := by
  dsimp [offset]
  rw [mul_comm,Int.ediv_mul_cancel hx]

/-- Actual integer lifting from modulus m to p*m. The quadratic error
term disappears because p divides m; the exact Taylor derivative and
actual quotient Q(x)/m, including its sign, remain in the residue test. -/
theorem actual_lift_iff (κ : ℤ) (p : ℕ) [NeZero p] (m : ℤ) (hm : m≠0)
    (hpm : (p:ℤ)∣m) (x : Coordinates ℤ) (hx : m∣equation κ x)
    (h : Coordinates (ZMod p)) :
    ((p:ℤ)*m)∣equation κ (translate x (digits p h) m) ↔
      (offset κ x m:ZMod p)+
        derivative (κ:ZMod p) (mapCoordinates (Int.castRingHom (ZMod p)) x) h=0 := by
  have hf : equation κ (translate x (digits p h) m)=
      m*(offset κ x m+derivative κ x (digits p h)+m*equation κ (digits p h)) := by
    rw [original_taylor,actual_offset_identity κ x m hx]
    ring
  rw [hf,mul_comm (p:ℤ) m,mul_dvd_mul_iff_left hm]
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hm0 : (m:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr hpm
  simp only [Int.cast_add,Int.cast_mul,hm0,zero_mul,add_zero,derivative_reduce]

/-- In particular the original p^e to p^(e+1) lifting test is produced
for every e>=1, not merely assumed for a smooth residue class. -/
theorem actual_prime_power_lift_iff (κ : ℤ) (p : ℕ) (hp : p.Prime) (e : ℕ) (he : 1≤e)
    (x : Coordinates ℤ) (hx : (p:ℤ)^e∣equation κ x) (h : Coordinates (ZMod p)) :
    (p:ℤ)^(e+1)∣equation κ (translate x (digits p h) ((p:ℤ)^e)) ↔
      (offset κ x ((p:ℤ)^e):ZMod p)+
        derivative (κ:ZMod p) (mapCoordinates (Int.castRingHom (ZMod p)) x) h=0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hd : (p:ℤ)∣(p:ℤ)^e := dvd_pow_self _ (by omega)
  have hh := actual_lift_iff κ p ((p:ℤ)^e) (pow_ne_zero e hp0) hd x hx h
  simpa only [pow_succ,mul_comm] using hh

end ActualOriginalModularLift318
