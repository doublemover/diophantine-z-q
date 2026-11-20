module
public import ActualAnchorAllPlaces318
public section
noncomputable section
namespace ActualAnchorTwoConics318
open ActualAnchorRatio318 PreparedAnchorLabels318 AnchorLocalSquareProduction318
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Integer numerator before any square-class or auxiliary-prime choice. -/
def num (r : ℚ) : ℤ := 3*r.num^2-2*(r.den:ℤ)^2

theorem reduced_eq (r : ℚ) :
    (3*r^2-2) = (num r:ℚ)/(r.den:ℚ)^2 := by
  have hd : (r.den:ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  calc 3*r^2-2 = 3*((r.num:ℚ)/(r.den:ℚ))^2-2 := by rw [Rat.num_div_den]
       _ = _ := by unfold num; push_cast; field_simp [hd] <;> ring

/-- Only integer congruences at the two exceptional primes are consumed. -/
theorem residue (r : ℚ) (hr : r≠0) (h2 : padicValRat 2 r=0)
    (h3 : 0≤padicValRat 3 r) : num r % 24 = 1 := by
  have hnu := odd_square_mod_eight _ (unit_two_num_odd r hr h2)
  have hd2 : ¬(2:ℤ) ∣ (r.den:ℤ) := by
    exact_mod_cast (denominator_unit 2 r (by omega))
  have hd3 : ¬(3:ℤ) ∣ (r.den:ℤ) := by
    exact_mod_cast (denominator_unit 3 r h3)
  rw [Int.dvd_iff_emod_eq_zero] at hd2 hd3
  have hrem : (r.den:ℤ)%12=1 ∨ (r.den:ℤ)%12=5 ∨
      (r.den:ℤ)%12=7 ∨ (r.den:ℤ)%12=11 := by omega
  have hd12 : (r.den:ℤ)^2%12=1 := by
    rw [show (r.den:ℤ)^2%12=((r.den:ℤ)%12)^2%12 by simp [pow_two,Int.mul_emod]]
    rcases hrem with H|H|H|H <;> rw [H] <;> norm_num
  unfold num
  omega

/-- Both outputs of the ternary-conic producer share exactly one multiplier.
The physical ternary ordinate may vanish; no affine chart on the second
conic is assumed. m = n*k², with k signed permitted. -/
structure Pair (m : ℤ) where
  n k : ℤ
  k_ne : k ≠ 0
  decomp : m=n*k^2
  ell X Y s z T : ℚ
  ell_pos : 0<ell
  first : X^2+6*Y^2=ell
  second : ell*s^2=2*z^2+(n:ℚ)*T^2
  nonzero : ¬(s=0 ∧ z=0 ∧ T=0)

theorem bind (r : ℚ) (P : Pair (num r)) :
    ∃ X Y Z T : ℚ, (¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) ∧
      X^2+6*Y^2-2*Z^2=(3*r^2-2)*T^2 := by
  let w : ℚ:=(P.k:ℚ)/(r.den:ℚ)
  have hk : (P.k:ℚ)≠0 := by exact_mod_cast P.k_ne
  have hd : (r.den:ℚ)≠0 := by exact_mod_cast r.den_ne_zero
  have hw : w≠0 := div_ne_zero hk hd
  have HC : 3*r^2-2=(P.n:ℚ)*w^2 := by
    rw [reduced_eq, P.decomp]
    unfold w
    push_cast
    ring
  refine ⟨w*P.X*P.s,w*P.Y*P.s,w*P.z,P.T,?_,?_⟩
  · rintro ⟨hX,hY,hZ,hT⟩
    have hz := (mul_eq_zero.mp hZ).resolve_left hw
    apply P.nonzero
    refine ⟨?_,hz,hT⟩
    by_contra hs
    have X0 : P.X=0 := (mul_eq_zero.mp ((mul_eq_zero.mp hX).resolve_right hs)).resolve_left hw
    have Y0 : P.Y=0 := (mul_eq_zero.mp ((mul_eq_zero.mp hY).resolve_right hs)).resolve_left hw
    have F:=P.first
    rw [X0,Y0] at F
    nlinarith [P.ell_pos]
  · rw [HC]
    linear_combination w^2*P.s^2*P.first+w^2*P.second

/-- Narrowed API: an integer congruence-class solver suffices. No assumed
global rank-four Hasse principle for arbitrary locally soluble forms. -/
theorem actual (arith : ∀ m : ℤ, m%24=1 → Nonempty (Pair m))
    (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    PhysicalAnchorFromHomogeneous318.Homogeneous
      (FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)) N := by
  let labels := FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)
  obtain ⟨hr,h2,h3⟩ := actual_anchor_depths a A B N d hd
  obtain ⟨P⟩ := arith (num (ratio labels N)) (residue (ratio labels N) hr h2 h3)
  exact bind (ratio labels N) P

end ActualAnchorTwoConics318
