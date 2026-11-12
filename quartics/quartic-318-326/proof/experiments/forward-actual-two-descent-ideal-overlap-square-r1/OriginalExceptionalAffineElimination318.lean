module
public import OriginalLinearNormEliminant318
public section
noncomputable section
namespace OriginalExceptionalAffineElimination318
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318 LiteralAdjacentNormSlice318
open OriginalNormPointSieveTail318 OriginalAffineSieveEliminants318
set_option maxHeartbeats 5000000

lemma field_branches {F : Type*} [Field F] (κ t x z w : F) (ht : t≠0) (ht2 : t+2=0)
    (hP : P' κ t (x,z,w)=0) (hD : D t (x,z,w)=0) :
    (x=0 ∧ t^2+z^2=0) ∨ (z=0 ∧ t^2+x^2=0) := by
  have htwo : (2:F)≠0 := by intro h;rw [h,add_zero] at ht2;exact ht ht2
  have hxz : x*z=0 := by
    have hh : (2:F)*(x*z)=0 := by
      simpa only [P',ht2,mul_zero,zero_mul,zero_sub,neg_eq_zero,mul_assoc] using hP
    exact (mul_eq_zero.mp hh).resolve_left htwo
  change (t^2+x^2)*(t^2+z^2)=0 at hD
  rcases mul_eq_zero.mp hxz with hx|hz
  · left
    refine ⟨hx,?_⟩
    rw [hx,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hD
    exact (mul_eq_zero.mp hD).resolve_left (pow_ne_zero _ ht)
  · right
    refine ⟨hz,?_⟩
    rw [hz,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hD
    exact (mul_eq_zero.mp hD).resolve_right (pow_ne_zero _ ht)

/-- Exact original integer axis/norm branches at t=-2, retaining the
free w coordinate and all actual primes outside t. -/
theorem actual_integer_branches (κ t : ℤ) (ht2 : t+2=0) (y : Vector ℤ)
    (p : ℕ) [Fact p.Prime] (ht : ¬(p:ℤ)∣t)
    (ho : pointObstruction true κ t y p) :
    ((p:ℤ)∣y.1 ∧ (p:ℤ)∣t^2+y.2.1^2) ∨
      ((p:ℤ)∣y.2.1 ∧ (p:ℤ)∣t^2+y.1^2) := by
  have htF : (t:ZMod p)≠0 := fun h => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
  have ht2F : (t:ZMod p)+2=0 := by
    have h := congrArg (Int.castRingHom (ZMod p)) ht2
    simpa using h
  have hP : P' (κ:ZMod p) (t:ZMod p) (reduce p y)=0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (P' κ t y) p).mpr ho.1
    simpa [P',reduce] using h
  have hD : D (t:ZMod p) (reduce p y)=0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (D t y) p).mpr ho.2
    simpa [D,reduce] using h
  have hb := field_branches (κ:ZMod p) (t:ZMod p) (y.1:ZMod p) (y.2.1:ZMod p)
    (y.2.2:ZMod p) htF ht2F hP hD
  rcases hb with ⟨hx,hz⟩|⟨hz,hx⟩
  · left
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx,?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add,Int.cast_pow] using hz
  · right
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz,?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add,Int.cast_pow] using hx

/-- The exceptional original second pair uses LINEAR/quadratic
eliminants, not the vanished padded quartic certificate. -/
theorem actual_exceptional_eliminates (κ t : ℤ) (ht2 : t+2=0) (a d : Vector ℤ)
    (h : ℤ) (p : ℕ) [Fact p.Prime] (ht : ¬(p:ℤ)∣t)
    (ho : pointObstruction true κ t (affine a d h) p) :
    (p:ℤ)∣OriginalLinearNormEliminant318.eliminant t a.1 a.2.1 d.1 d.2.1 ∨
      (p:ℤ)∣OriginalLinearNormEliminant318.eliminant t a.2.1 a.1 d.2.1 d.1 := by
  rcases actual_integer_branches κ t ht2 (affine a d h) p ht ho with hx|hz
  · left
    apply OriginalLinearNormEliminant318.divisor _ _ _ _ _ h _
    · simpa [affine,zsmul_eq_mul] using hx.1
    · simpa [affine,zsmul_eq_mul,add_comm] using hx.2
  · right
    apply OriginalLinearNormEliminant318.divisor _ _ _ _ _ h _
    · simpa [affine,zsmul_eq_mul] using hz.1
    · simpa [affine,zsmul_eq_mul,add_comm] using hz.2

end OriginalExceptionalAffineElimination318
