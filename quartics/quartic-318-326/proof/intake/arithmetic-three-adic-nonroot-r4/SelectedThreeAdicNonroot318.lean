module
public import SelectedThreeAdicEscape318
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace SelectedThreeAdicNonroot318
open SelectedThreeAdicEscape318

private theorem square_int (q : ℚ) (z : ℤ) (h : q^2=(z:ℚ)) :
    ∃ u : ℤ, u^2=z := by
  obtain ⟨u,hu⟩ := Rat.isSquare_intCast_iff.mp
    (show IsSquare (z:ℚ) from ⟨q, by simpa only [pow_two] using h.symm⟩)
  exact ⟨u,by simpa only [pow_two] using hu.symm⟩

/-- A genuinely 3-adic step. If 3 does not divide b, the square equations
force 3|a and 3|t; cancellation of ONE factor of 3 in the second
integer equality then gives n*b²=0 mod 3, a contradiction. -/
private theorem den_dvd {n a b s t : ℤ} (hn : (n:ZMod 3)=2)
    (hs : s^2=a^2-n*b^2) (ht : t^2=a^2+3*n*b^2) : (3:ℤ) ∣ b := by
  by_contra h
  have hb : (b:ZMod 3) ≠ 0 := fun he => h ((ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp he)
  have hs3 := congrArg (fun k : ℤ => (k:ZMod 3)) hs
  have ht3 := congrArg (fun k : ℤ => (k:ZMod 3)) ht
  push_cast at hs3 ht3
  rw [hn] at hs3
  have units : ∀ a b s : ZMod 3, b ≠ 0 → s^2=a^2-2*b^2 → a=0 := by decide +kernel
  have ha := units _ _ _ hb hs3
  have hzero3 : (3:ZMod 3)=0 := by decide
  have ht0 : (t:ZMod 3)=0 := by
    have eqt : (t:ZMod 3)^2=0 := by rw [ht3,ha,hzero3] <;> ring
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp eqt
  obtain ⟨a',ha'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
  obtain ⟨t',ht'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t 3).mp ht0
  have hc : 3*t'^2=3*a'^2+n*b^2 := by
    rw [ha',ht'] at ht
    linarith only [show 3*(3*t'^2-(3*a'^2+n*b^2))=0 by linear_combination ht]
  have h3 := congrArg (fun k : ℤ => (k:ZMod 3)) hc
  push_cast at h3
  rw [hn] at h3
  have hnb : (2:ZMod 3)*(b:ZMod 3)^2 ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero _ hb)
  simp only [hzero3,zero_mul,zero_add] at h3
  exact hnb h3.symm

theorem seed_of_square_coordinates (n : ℤ) (hn : (n:ZMod 3)=2)
    (r s t : ℚ) (hs : s^2=r^2-n) (ht : t^2=r^2+3*n) : Nonempty (Seed n) := by
  let a := r.num
  let b : ℤ := r.den
  have hb : b ≠ 0 := by
    change (r.den:ℤ) ≠ 0
    exact_mod_cast r.den_nz
  have hbq : (b:ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hr : r*(b:ℚ)=(a:ℚ) := by
    dsimp [a,b]
    simpa only [Int.cast_natCast] using (eq_div_iff (by exact_mod_cast r.den_nz :
      (r.den:ℚ) ≠ 0)).mp (Rat.num_div_den r).symm
  obtain ⟨u,hu⟩ := square_int (s*b) (a^2-n*b^2) (by
    push_cast
    rw [mul_pow,hs,← hr]
    ring)
  obtain ⟨v,hv⟩ := square_int (t*b) (a^2+3*n*b^2) (by
    push_cast
    rw [mul_pow,ht,← hr]
    ring)
  obtain ⟨k,hk⟩ := den_dvd hn hu hv
  have hkq : (b:ℚ)=3*(k:ℚ) := by exact_mod_cast hk
  have ha : (a:ZMod 3) ≠ 0 := by
    intro he
    have hda := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp he
    have hd1 : 3 ∣ r.num.natAbs := by
      obtain ⟨w,hw⟩ := hda
      exact ⟨w.natAbs,by dsimp [a] at hw; rw [hw,Int.natAbs_mul]; rfl⟩
    have hd2 : 3 ∣ r.den := by
      change (r.den:ℤ)=3*k at hk
      exact_mod_cast (show (3:ℤ) ∣ (r.den:ℤ) from ⟨k,hk⟩)
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) hd1 hd2) r.reduced
  have hk0 : k ≠ 0 := by intro hh; rw [hh,mul_zero] at hk; exact hb hk
  refine ⟨⟨a^2,k^2,r*s*t,?_,pow_ne_zero _ hk0,?_⟩⟩
  · push_cast
    exact pow_ne_zero _ ha
  · push_cast
    rw [← hr,hkq]
    simp only [mul_pow,hs,ht]
    ring

/-- For any non-root, these are the three genuine square coordinates of its
double, but we need no identification of formal group laws: the displayed
polynomial identities themselves give the point. -/
theorem seed_of_nonroot (n : ℤ) (hn : (n:ZMod 3)=2) (x y : ℚ)
    (hy : y ≠ 0) (he : y^2=x*(x-n)*(x+3*n)) : Nonempty (Seed n) := by
  let r := (x^2+3*(n:ℚ)^2)/(2*y)
  let s := (x^2-2*n*x-3*(n:ℚ)^2)/(2*y)
  let t := (x^2+6*n*x-3*(n:ℚ)^2)/(2*y)
  apply seed_of_square_coordinates n hn r s t
  · dsimp only [s,r]
    field_simp [hy]
    linear_combination (4*(n:ℚ))*he
  · dsimp only [t,r]
    field_simp [hy]
    linear_combination (-12*(n:ℚ))*he
/-- Stock-only endpoint: actual rational affine solutions, not merely a
sequence of abstract putative classes. -/
theorem infinite_affine_of_nonroot (n : ℤ) (hn : (n:ZMod 3)=2) (x y : ℚ)
    (hy : y ≠ 0) (he : y^2=x*(x-n)*(x+3*n)) :
    Infinite {xy : ℚ × ℚ // xy.2^2 = xy.1*(xy.1-n)*(xy.1+3*n)} := by
  obtain ⟨s⟩ := seed_of_nonroot n hn x y hy he
  let f (k : ℕ) : {xy : ℚ × ℚ // xy.2^2 = xy.1*(xy.1-n)*(xy.1+3*n)} :=
    ⟨((iter s k).x,(iter s k).y),(iter s k).onCurve⟩
  apply Infinite.of_injective f
  intro i j h
  apply iter_x_injective s
  exact congrArg (fun p : {xy : ℚ × ℚ // xy.2^2=xy.1*(xy.1-n)*(xy.1+3*n)} => p.val.1) h

end SelectedThreeAdicNonroot318
