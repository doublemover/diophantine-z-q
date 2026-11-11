module
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic
public section
namespace NormalizerVertexEnergyBounds318
set_option maxHeartbeats 2000000
/-- Twenty times the original affine height denominator at (28,1), after
s=2a+c,r=2b+d in the original order coordinates. -/
@[expose] def energy0 (s r c d : ℤ) : ℤ :=
  5*s^2+1050*r^2+25*c^2+210*d^2+56*s*d-280*r*c+10*s*c+420*r*d
/-- Twenty-eight times the original affine height denominator at (30,5/7).
Both forms here are FOUR times the actual denominator times5 or7. -/
@[expose] def energy1 (s r c d : ℤ) : ℤ :=
  7*s^2+1470*r^2+35*c^2+294*d^2+84*s*d-420*r*c+10*s*c+420*r*d

/-- Exact positive-square certificates bound the entire integer lattice,
BEFORE any finite search. No normalizer enumeration is assumed. -/
theorem energy0_bounds (s r c d : ℤ) :
    56*r^2≤energy0 s r c d ∧ 4*c^2≤3*energy0 s r c d ∧ 56*d^2≤5*energy0 s r c d := by
  have h1 : 0≤5*(energy0 s r c d-56*r^2) := by
    calc
      _ = (5*c+28*d+5*s)^2+4*(5*c-7*d-35*r)^2+70*(d+r)^2 := by unfold energy0; ring
      _ ≥ 0 := by positivity
  have h2 : 0≤5*(3*energy0 s r c d-4*c^2) := by
    calc
      _ = 3*(5*c+28*d+5*s)^2+70*(-2*c+3*d+15*r)^2+168*d^2 := by unfold energy0; ring
      _ ≥ 0 := by positivity
  have h3 : 0≤3*(5*energy0 s r c d-56*d^2) := by
    calc
      _ = 3*(5*c+28*d+5*s)^2+70*(-2*c+3*d+15*r)^2+20*c^2 := by unfold energy0; ring
      _ ≥ 0 := by positivity
  exact ⟨by linarith,by linarith,by linarith⟩

theorem energy1_bounds (s r c d : ℤ) :
    60*r^2≤energy1 s r c d ∧ 10*c^2≤7*energy1 s r c d ∧ 12*d^2≤energy1 s r c d := by
  have h1 : 0≤77*(energy1 s r c d-60*r^2) := by
    calc
      _ = 11*(5*c+42*d+7*s)^2+5*(22*c-21*d-147*r)^2+21*(7*d+5*r)^2 := by unfold energy1; ring
      _ ≥ 0 := by positivity
  have h2 : 0≤7*energy1 s r c d-10*c^2 := by
    calc
      _ = (5*c+42*d+7*s)^2+210*(-c+d+7*r)^2+84*d^2 := by unfold energy1; ring
      _ ≥ 0 := by positivity
  have h3 : 0≤7*(energy1 s r c d-12*d^2) := by
    calc
      _ = (5*c+42*d+7*s)^2+210*(-c+d+7*r)^2+10*c^2 := by unfold energy1; ring
      _ ≥ 0 := by positivity
  exact ⟨by linarith,by linarith,by linarith⟩

theorem natAbs_bound (z : ℤ) (C N : ℕ) (hC : 0<C)
    (h : (C:ℤ)*z^2≤(N:ℤ)) : z.natAbs≤Nat.sqrt (N/C) := by
  have hz : (C:ℤ)*((z.natAbs:ℤ)^2)≤(N:ℤ) := by
    simpa only [Int.natCast_natAbs,sq_abs] using h
  have hn : C*z.natAbs^2≤N := by exact_mod_cast hz
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le hC).mpr
  simpa only [mul_comm] using hn
end NormalizerVertexEnergyBounds318
