module
public import Height13RealLog
public import Mathlib.Data.ZMod.Basic
public section
namespace AnchorAnisotropy

private theorem outer_residues : ∀ x y z : ZMod 3,
    x^2+6*y^2-2*z^2=0 → x=0 ∧ z=0 := by decide

private theorem middle_residue : ∀ x y z : ZMod 3,
    2*y^2+3*x^2-6*z^2=0 → y=0 := by decide

/-- Every integral zero of the ternary anchor form is divisible by three in
all coordinates. This is the exact descent obstruction, not a bound check. -/
theorem coordinates_divisible_three (x y z : ℤ)
    (h : x^2+6*y^2-2*z^2=0) : (3:ℤ)∣x ∧ (3:ℤ)∣y ∧ (3:ℤ)∣z := by
  have hm : (x:ZMod 3)^2+6*(y:ZMod 3)^2-2*(z:ZMod 3)^2=0 := by
    have hh := congrArg (fun t : ℤ => (t : ZMod 3)) h
    push_cast at hh
    exact hh
  obtain ⟨hx,hz⟩ := outer_residues _ _ _ hm
  have hdx : (3:ℤ)∣x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx
  have hdz : (3:ℤ)∣z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hz
  obtain ⟨a,ha⟩ := hdx
  obtain ⟨c,hc⟩ := hdz
  have hn : 2*y^2+3*a^2-6*c^2=0 := by rw [ha,hc] at h; nlinarith [h]
  have hnm : 2*(y:ZMod 3)^2+3*(a:ZMod 3)^2-6*(c:ZMod 3)^2=0 := by
    have hh := congrArg (fun t : ℤ => (t : ZMod 3)) hn
    push_cast at hh
    exact hh
  have hdy : (3:ℤ)∣y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp (middle_residue _ _ _ hnm)
  exact ⟨⟨a,ha⟩,hdy,⟨c,hc⟩⟩

private theorem integer_descent (n : ℕ) : ∀ x y z : ℤ,
    x.natAbs+y.natAbs+z.natAbs=n → x^2+6*y^2-2*z^2=0 →
      x=0 ∧ y=0 ∧ z=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y z hn hq
    by_cases hz : n=0
    · have hx : x.natAbs=0 := by omega
      have hy : y.natAbs=0 := by omega
      have hz' : z.natAbs=0 := by omega
      exact ⟨Int.natAbs_eq_zero.mp hx,Int.natAbs_eq_zero.mp hy,Int.natAbs_eq_zero.mp hz'⟩
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩ := coordinates_divisible_three x y z hq
    rw [ha,hb,hc] at hn hq ⊢
    have hsmall : a^2+6*b^2-2*c^2=0 := by nlinarith [hq]
    have hn3 : 3*(a.natAbs+b.natAbs+c.natAbs)=n := by
      simpa [Int.natAbs_mul, Nat.mul_add] using hn
    have hlt : a.natAbs+b.natAbs+c.natAbs<n := by omega
    obtain ⟨ha0,hb0,hc0⟩ := ih _ hlt a b c rfl hsmall
    simp [ha0,hb0,hc0]

/-- Rational anisotropy is proved below by clearing denominators; this integral
version supplies its well-founded infinite descent. -/
theorem integer_anisotropic (x y z : ℤ) (h : x^2+6*y^2-2*z^2=0) :
    x=0 ∧ y=0 ∧ z=0 := integer_descent _ x y z rfl h

/-- The physical anchor's ternary form is anisotropic over the rationals.
No local-field, quadratic-form local-global, or elliptic hypothesis is used. -/
theorem rational_anisotropic (x y z : ℚ) (h : x^2+6*y^2-2*z^2=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  let X : ℤ := x.num * y.den * z.den
  let Y : ℤ := y.num * x.den * z.den
  let Z : ℤ := z.num * x.den * y.den
  let D : ℚ := (x.den : ℚ) * (y.den : ℚ) * (z.den : ℚ)
  have hx : (X:ℚ)=x*D := by
    dsimp [X,D]
    push_cast
    rw [← Rat.mul_den_eq_num x]
    ring
  have hy : (Y:ℚ)=y*D := by
    dsimp [Y,D]
    push_cast
    rw [← Rat.mul_den_eq_num y]
    ring
  have hz : (Z:ℚ)=z*D := by
    dsimp [Z,D]
    push_cast
    rw [← Rat.mul_den_eq_num z]
    ring
  have hscaled : (X:ℚ)^2+6*(Y:ℚ)^2-2*(Z:ℚ)^2=0 := by
    rw [hx,hy,hz]
    linear_combination D^2*h
  have hint : X^2+6*Y^2-2*Z^2=0 := by exact_mod_cast hscaled
  obtain ⟨hX,hY,hZ⟩ := integer_anisotropic X Y Z hint
  have hdX : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hdY : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
  have hdZ : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_nz
  have hD : D≠0 := mul_ne_zero (mul_ne_zero hdX hdY) hdZ
  have hxD : x*D=0 := by rw [← hx,hX]; simp
  have hyD : y*D=0 := by rw [← hy,hY]; simp
  have hzD : z*D=0 := by rw [← hz,hZ]; simp
  exact ⟨(mul_eq_zero.mp hxD).resolve_right hD,
    (mul_eq_zero.mp hyD).resolve_right hD,(mul_eq_zero.mp hzD).resolve_right hD⟩

/-- A nonzero rational zero of the homogenized anchor form necessarily lies
in the affine chart T≠0. This discharges the anisotropy premise of the source's
homogeneous-to-affine construction. -/
theorem homogeneous_denominator_nonzero (c X Y Z T : ℚ)
    (hQ : X^2+6*Y^2-2*Z^2=c*T^2)
    (hnonzero : ¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) : T≠0 := by
  intro hT
  have hzero : X^2+6*Y^2-2*Z^2=0 := by simpa [hT] using hQ
  obtain ⟨hX,hY,hZ⟩ := rational_anisotropic X Y Z hzero
  exact hnonzero ⟨hX,hY,hZ,hT⟩

/-- Only the homogeneous rational solution is needed from local-global theory;
the affine chart is now justified unconditionally. -/
theorem rational_representation_of_homogeneous (c : ℚ)
    (hsol : ∃ X Y Z T : ℚ,
      (¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) ∧ X^2+6*Y^2-2*Z^2=c*T^2) :
    ∃ x y z : ℚ, x^2+6*y^2-2*z^2=c := by
  obtain ⟨X,Y,Z,T,hn,hQ⟩ := hsol
  have hT := homogeneous_denominator_nonzero c X Y Z T hQ hn
  refine ⟨X/T,Y/T,Z/T,?_⟩
  field_simp
  simpa [mul_comm] using hQ

/-- Source-facing physical anchor, conditional only on the rational homogeneous
zero supplied by the separate local-global theorem. -/
theorem physical_anchor_of_homogeneous (A S : ℚ) (hS : S≠0)
    (hsol : ∃ X Y Z T : ℚ,
      (¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) ∧
        X^2+6*Y^2-2*Z^2=(3*(A/S)^2-2)*T^2) :
    ∃ u v w : ℚ, u^2+6*v^2-2*w^2-3*A^2+2*S^2=0 := by
  obtain ⟨x,y,z,hr⟩ := rational_representation_of_homogeneous _ hsol
  refine ⟨S*x,S*y,S*z,?_⟩
  field_simp at hr
  linear_combination hr

#print axioms coordinates_divisible_three
#print axioms integer_anisotropic
#print axioms rational_anisotropic
#print axioms homogeneous_denominator_nonzero
#print axioms rational_representation_of_homogeneous
#print axioms physical_anchor_of_homogeneous
end AnchorAnisotropy
