module
public import Height13RealLog
public section
namespace BranchHalving
variable {F : Type*} [Field F]

/-- On the source curve over any good residue field, a square root of 1+r
supplies the other nontrivial descent root r/a without any extra choice. -/
theorem half_parameter (r a : F) (hr : r^2=2) (ha : a^2=1+r) :
    a ≠ 0 ∧ (a+r/a)^2=5*r-1 := by
  have ha0 : a ≠ 0 := by
    intro h
    have hr1 : r = -1 := by rw [h] at ha; linear_combination -ha
    have hrplus : r+1=0 := by rw [hr1]; ring
    have h01 : (0:F)=1 := by linear_combination hr - (r-1)*hrplus
    exact zero_ne_one h01
  refine ⟨ha0, ?_⟩
  apply (mul_right_inj' (pow_ne_zero 2 ha0)).mp
  field_simp
  linear_combination (a^2-2*r+2)*ha - hr

/-- Polynomial certificate for an explicit half of R₀=(1+r,2r).
The last two equalities are exactly the affine duplication formulas. -/
theorem half_identities (r u : F) (hr : r^2=2) (hu : u^2=5*r-1) :
    let D := (3-r)^2
    let x := 1+2*r-2*u
    let y := -2+10*r-(r+4)*u
    let m := 2-u
    y^2=x^3-D*x ∧ 2*y*m=3*x^2-D ∧
      m^2-2*x=1+r ∧ m*(x-(1+r))-y=2*r := by
  dsimp
  constructor
  · linear_combination (r^2-16*r+8*u+4)*hu + (-r+2*u-4)*hr
  constructor
  · linear_combination (2*r-4)*hu - hr
  constructor
  · linear_combination hu
  · linear_combination 2*hu

/-- The denominator of the tangent formula does not vanish at a good prime.
This uses exactly characteristics other than 2 and 7, not characteristic zero. -/
theorem half_y_nonzero (r u : F) (hr : r^2=2) (hu : u^2=5*r-1)
    (h2 : (2:F) ≠ 0) (h7 : (7:F) ≠ 0) :
    -2+10*r-(r+4)*u ≠ 0 := by
  let D := (3-r)^2
  let x := 1+2*r-2*u
  let y := -2+10*r-(r+4)*u
  let m := 2-u
  have H := half_identities r u hr hu
  change y^2=x^3-D*x ∧ 2*y*m=3*x^2-D ∧ _ at H
  have hD : D≠0 := by
    intro hd
    have hs : 3-r=0 := (sq_eq_zero_iff).mp hd
    apply h7
    linear_combination hr + (r+3)*hs
  intro hy
  change y=0 at hy
  have hd : D=3*x^2 := by linear_combination H.2.1 - 2*m*hy
  have hx3 : 2*x^3=0 := by linear_combination H.1 - x*hd - y*hy
  have hx : x=0 := (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).mp (mul_eq_zero.mp hx3 |>.resolve_left h2)
  apply hD
  simpa [hx] using hd

/-- Algebraic residue-symbol bridge: a primitive-sixteenth-root candidate
and a fourth root of 2 force 1+r to be a square, for either root r of 2.
Existence of those roots at selected primes is the external arithmetic input. -/
theorem epsilon_square_from_roots (r z t : F) (hr : r^2=2)
    (hz : z^8 = -1) (ht : t^4=2) (h2 : (2:F) ≠ 0) :
    ∃ a : F, a^2=1+r := by
  have hz0 : z≠0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz
    exact (neg_ne_zero.mpr one_ne_zero) hz.symm
  have hr0 : r≠0 := by intro h; rw [h, zero_pow (by decide)] at hr; exact h2 hr.symm
  let i := z^4
  have hi : i^2 = -1 := by dsimp [i]; simpa [← pow_mul] using hz
  obtain ⟨s, hs⟩ : ∃ s : F, s^2=r := by
    have ht2 : r^2=(t^2)^2 := by rw [hr, ← pow_mul]; exact ht.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp ht2) with h | h
    · exact ⟨t, h.symm⟩
    · refine ⟨i*t, ?_⟩
      rw [mul_pow, hi, neg_one_mul]
      exact h.symm
  let q := z^2+1/z^2
  have hq : q^2=2 := by
    dsimp [q]
    field_simp
    linear_combination hz
  let bp := z+1/z
  let bm := i*(z-1/z)
  have hbp : bp^2=2+q := by
    dsimp [bp, q]
    field_simp
    ring
  have hbm : bm^2=2-q := by
    have hv : (z-1/z)^2=q-2 := by
      dsimp [q]
      field_simp
      ring
    dsimp [bm]
    rw [mul_pow, hi, hv]
    ring
  have hquot (b : F) (hb : b^2=2+r) : (b/s)^2=1+r := by
    rw [div_pow, hb, hs]
    apply (div_eq_iff hr0).mpr
    linear_combination -hr
  have hqr : q=r ∨ q= -r := sq_eq_sq_iff_eq_or_eq_neg.mp (hq.trans hr.symm)
  rcases hqr with h | h
  · exact ⟨bp/s, hquot bp (by simpa [h] using hbp)⟩
  · exact ⟨bm/s, hquot bm (by simpa [h] using hbm)⟩

/-- Constructive, domain-checked doubling-image witness for the source's R₀.
The remaining number-theoretic premise is that 1+r is a residue-field square. -/
theorem explicit_half (r a : F) (hr : r^2=2) (ha : a^2=1+r)
    (h2 : (2:F) ≠ 0) (h7 : (7:F) ≠ 0) :
    ∃ x y m : F, y ≠ 0 ∧
      y^2=x^3-(3-r)^2*x ∧ 2*y*m=3*x^2-(3-r)^2 ∧
      m^2-2*x=1+r ∧ m*(x-(1+r))-y=2*r := by
  let u := a+r/a
  have hu := (half_parameter r a hr ha).2
  exact ⟨1+2*r-2*u, -2+10*r-(r+4)*u, 2-u,
    half_y_nonzero r u hr hu h2 h7, half_identities r u hr hu⟩

/-- Combined square-root and halving certificate, valid in the selected finite
residue fields. No characteristic-zero or analytic hypothesis is hidden here. -/
theorem explicit_half_from_roots (r z t : F) (hr : r^2=2)
    (hz : z^8 = -1) (ht : t^4=2)
    (h2 : (2:F) ≠ 0) (h7 : (7:F) ≠ 0) :
    ∃ x y m : F, y ≠ 0 ∧
      y^2=x^3-(3-r)^2*x ∧ 2*y*m=3*x^2-(3-r)^2 ∧
      m^2-2*x=1+r ∧ m*(x-(1+r))-y=2*r := by
  obtain ⟨a, ha⟩ := epsilon_square_from_roots r z t hr hz ht h2
  exact explicit_half r a hr ha h2 h7

#print axioms half_parameter
#print axioms explicit_half
#print axioms epsilon_square_from_roots
#print axioms explicit_half_from_roots
end BranchHalving
