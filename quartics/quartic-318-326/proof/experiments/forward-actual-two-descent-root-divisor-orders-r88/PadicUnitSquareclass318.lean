module
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic
public section
noncomputable section
namespace PadicUnitSquareclass318
open Polynomial
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Hensel supplies an actual nonzero square multiplier, not merely a residue
square. The unit and error conditions are precisely those used below. -/
theorem square_multiplier (p : ℕ) [Fact p.Prime] (u v : ℤ_[p])
    (hu : ‖u‖=1) (hclose : ‖u-v‖<‖(2:ℤ_[p])‖^2) :
    ∃ s : ℤ_[p], s≠0 ∧ v=u*s^2 := by
  let F : Polynomial ℤ_[p] := C u*X^2-C v
  have heval : F.aeval (1:ℤ_[p])=u-v := by simp [F]
  have hderiv : F.derivative.aeval (1:ℤ_[p])=2*u := by
    dsimp only [F]
    rw [derivative_sub,derivative_C,derivative_C_mul_X_sq]
    norm_num
    <;> ring
  have hder : ‖F.derivative.aeval (1:ℤ_[p])‖=‖(2:ℤ_[p])‖ := by
    rw [hderiv,norm_mul,hu,mul_one]
  have hn : ‖F.aeval (1:ℤ_[p])‖<‖F.derivative.aeval (1:ℤ_[p])‖^2 := by
    simpa only [heval,hder] using hclose
  obtain ⟨s,hs,hsclose,_⟩ := hensels_lemma hn
  have hs0 : s≠0 := by
    intro h
    rw [hder,h] at hsclose
    have hh : (1:ℝ)<‖(2:ℤ_[p])‖ := by simpa using hsclose
    exact (not_lt_of_ge (PadicInt.norm_le_one _)) hh
  refine ⟨s,hs0,?_⟩
  have hh : u*s^2-v=0 := by simpa [F] using hs
  exact (sub_eq_zero.mp hh).symm

/-- At an odd prime, equality modulo p preserves the squareclass of a unit. -/
theorem odd_prime (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (u v : ℤ_[p]) (hu : ‖u‖=1) (h : (p:ℤ_[p])∣u-v) :
    ∃ s : ℤ_[p], s≠0 ∧ v=u*s^2 := by
  have hp : p.Prime := Fact.out
  have hnot : ¬p∣2 := by
    intro hd
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hp.ne_one)
  have htwo : ‖(2:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr hnot
  apply square_multiplier p u v hu
  rw [htwo,one_pow]
  exact (PadicInt.norm_lt_one_iff_dvd _).mpr h

/-- At 2, equality modulo 8 preserves the squareclass of a unit. The stronger
modulus is needed because the derivative has norm 1/2, not norm 1. -/
theorem dyadic (u v : ℤ_[2]) (hu : ‖u‖=1) (h : (8:ℤ_[2])∣u-v) :
    ∃ s : ℤ_[2], s≠0 ∧ v=u*s^2 := by
  obtain ⟨w,hw⟩ := h
  have htwo : ‖(2:ℤ_[2])‖=(1/2:ℝ) := by simpa using (PadicInt.norm_p (p:=2))
  have height : ‖(8:ℤ_[2])‖=(1/8:ℝ) := by
    rw [show (8:ℤ_[2])=(2:ℤ_[2])^3 by norm_num,norm_pow,htwo]
    norm_num
  apply square_multiplier 2 u v hu
  rw [hw,norm_mul,height,htwo]
  have hn := PadicInt.norm_le_one w
  nlinarith

/-- Extract a genuine integer unit residue at every positive depth. The
representative is the native p-adic approximation; no residue-unit assumption
is added. -/
theorem unit_residue (p : ℕ) [Fact p.Prime] (u : ℤ_[p])
    (hu : ‖u‖=1) (k : ℕ) (hk : 0<k) :
    ∃ n : ℕ, ¬p∣n ∧ u-(n:ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k} := by
  let n := u.appr k
  have hmem : u-(n:ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k} := PadicInt.appr_spec k u
  have hdiv : (p:ℤ_[p])∣u-(n:ℤ_[p]) :=
    dvd_trans (dvd_pow_self _ (Nat.ne_of_gt hk)) (Ideal.mem_span_singleton.mp hmem)
  have hd : ‖u-(n:ℤ_[p])‖<1 := (PadicInt.norm_lt_one_iff_dvd _).mpr hdiv
  have hn : ‖(n:ℤ_[p])‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    apply le_of_not_gt
    intro hnlt
    have hb := PadicInt.nonarchimedean (u-(n:ℤ_[p])) (n:ℤ_[p])
    have hlt := lt_of_le_of_lt hb (max_lt hd hnlt)
    have hbad : (1:ℝ)<1 := by simpa only [sub_add_cancel,hu] using hlt
    exact (lt_irrefl (1:ℝ)) hbad
  exact ⟨n,PadicInt.norm_natCast_eq_one_iff.mp hn,hmem⟩

/-- Any integer in the extracted residue class has the same p-adic congruence.
This is the bridge from integer CRT output back to the original local unit. -/
theorem preserve_residue (p : ℕ) [Fact p.Prime] (u : ℤ_[p])
    (k : ℕ) (n m : ℤ)
    (hn : u-(n:ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k})
    (hm : (p:ℤ)^k∣m-n) :
    u-(m:ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k} := by
  obtain ⟨c,hc⟩ := hm
  have hdiff : (m:ℤ_[p])-(n:ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(c:ℤ_[p]),?_⟩
    exact_mod_cast hc
  convert Ideal.sub_mem _ hn hdiff using 1 <;> ring

end PadicUnitSquareclass318
