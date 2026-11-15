module
public import ActualOriginalPositiveRayScaling318
public section
noncomputable section
namespace ActualOriginalPrimitiveRayFactor318
open QuadricCRTAssembly318 ActualOriginalPositiveRayScaling318
open ActualPrimePointPrimitivity318 ActualPrimitiveResidueMap318

/-- A nonprimitive point has a literal prime factor in ALL five
coordinates. Dividing those original coordinates preserves the equation
and strictly lowers the positive first coordinate. -/
lemma actual_prime_ray_descent (κ : ℤ) (v : Quadric κ) (ha : 0<v.1.1.1)
    (hv : ¬Primitive κ v) :
    ∃ p : ℕ, p.Prime ∧ ∃ u : Quadric κ, 0<u.1.1.1 ∧
      u.1.1.1.natAbs<v.1.1.1.natAbs ∧ v.1=scaleCoordinates (p : ℤ) u.1 := by
  unfold Primitive at hv
  push_neg at hv
  obtain ⟨p,hp,hzero⟩ := hv
  obtain ⟨⟨ha0,hb0⟩,⟨hc0,hd0⟩,hw0⟩ := (reduction_eq_origin_iff κ p v).mp hzero
  obtain ⟨a,ha'⟩ := ha0
  obtain ⟨b,hb'⟩ := hb0
  obtain ⟨c,hc'⟩ := hc0
  obtain ⟨d,hd'⟩ := hd0
  obtain ⟨w,hw'⟩ := hw0
  let z : Coordinates ℤ := ((a,b),(c,d),w)
  have he : v.1=scaleCoordinates (p : ℤ) z := by
    apply Prod.ext
    · exact Prod.ext ha' hb'
    · exact Prod.ext (Prod.ext hc' hd') hw'
  have hpz : (0 : ℤ)<p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℤ)≤p := by exact_mod_cast hp.two_le
  have hpa : 0<(p : ℤ)*a := by rwa [←ha']
  have hza : 0<a := (mul_pos_iff_of_pos_left hpz).mp hpa
  have hsmall : a<v.1.1.1 := by
    have hh := mul_le_mul_of_nonneg_right hp2 (le_of_lt hza)
    nlinarith [ha']
  have haabs : (a.natAbs : ℤ)=a := by rw [Int.natCast_natAbs,abs_of_pos hza]
  have hvabs : (v.1.1.1.natAbs : ℤ)=v.1.1.1 := by rw [Int.natCast_natAbs,abs_of_pos ha]
  have hsmall' : a.natAbs<v.1.1.1.natAbs := by exact_mod_cast (show (a.natAbs : ℤ)<v.1.1.1.natAbs by omega)
  have hz : equation κ z=0 := by
    have hh := v.2
    rw [he,actual_equation_scale] at hh
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 (ne_of_gt hpz))
  exact ⟨p,hp,⟨z,hz⟩,hza,hsmall',he⟩

/-- Actual global primitive factor on the SAME positive integer ray.
Strong descent terminates by the original positive coordinate. No prime
point or finite-prime sieve hypothesis is needed. -/
theorem actual_primitive_ray_factor (κ : ℤ) (v : Quadric κ) (ha : 0<v.1.1.1) :
    ∃ d : ℕ, 0<d ∧ ∃ u : Quadric κ, Primitive κ u ∧ 0<u.1.1.1 ∧
      v.1=scaleCoordinates (d : ℤ) u.1 := by
  classical
  have h : ∀ m : ℕ, ∀ z : Quadric κ, z.1.1.1.natAbs=m → 0<z.1.1.1 →
      ∃ d : ℕ, 0<d ∧ ∃ u : Quadric κ, Primitive κ u ∧ 0<u.1.1.1 ∧
        z.1=scaleCoordinates (d : ℤ) u.1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro z hm hza
      by_cases hz : Primitive κ z
      · exact ⟨1,by norm_num,z,hz,hza,(actual_scale_one z.1).symm⟩
      · obtain ⟨q,hq,z',hz'a,hlt,he⟩ := actual_prime_ray_descent κ z hza hz
        obtain ⟨d,hd,u,hu,hua,hfactor⟩ := ih z'.1.1.1.natAbs (by omega) z' rfl hz'a
        refine ⟨q*d,mul_pos hq.pos hd,u,hu,hua,?_⟩
        rw [he,hfactor,actual_scale_mul,Nat.cast_mul]
  exact h v.1.1.1.natAbs v rfl ha

end ActualOriginalPrimitiveRayFactor318
