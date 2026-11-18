module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic
public section
namespace LegendreSquarefreeCRT318

/-- Signed squarefree normalization does not increase coefficient size. -/
theorem normalize (n : ℤ) (hn : n≠0) :
    ∃ e d : ℤ, e≠0 ∧ d≠0 ∧ e^2*d=n ∧ Squarefree d ∧ |d|≤|n| := by
  obtain ⟨e,d,he,hd⟩ := exists_sq_mul_squarefree n
  have he0 : e≠0 := by
    intro h
    apply hn
    simpa [h] using he.symm
  have hd0 : d≠0 := by
    intro h
    apply hn
    simpa [h] using he.symm
  have hdvd : d∣n := ⟨e^2,by rw [←he]; ring⟩
  have hle : d.natAbs≤n.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr hdvd)
  refine ⟨e,d,he0,hd0,he,hd,?_⟩
  have hleZ : (d.natAbs:ℤ)≤(n.natAbs:ℤ) := by exact_mod_cast hle
  simpa only [Int.natCast_natAbs] using hleZ

/-- Chinese remainder combines actual roots for coprime moduli. -/
theorem square_mul (a : ℤ) {m n : ℕ} (hcop : m.Coprime n)
    (hm : IsSquare (a : ZMod m)) (hn : IsSquare (a : ZMod n)) :
    IsSquare (a : ZMod (m*n)) := by
  have hprod : IsSquare (a : ZMod m × ZMod n) := by
    obtain ⟨x,hx⟩ := hm
    obtain ⟨y,hy⟩ := hn
    exact ⟨(x,y),Prod.ext hx hy⟩
  simpa only [map_intCast] using hprod.map (ZMod.chineseRemainder hcop).symm

/-- Prime-by-prime modular roots produce a root modulo a squarefree modulus.
No compatibility or coprimality premise is left to the caller. -/
theorem square_mod_squarefree (a : ℤ) (n : ℕ) (hn : Squarefree n)
    (hlocal : ∀ p : ℕ, p.Prime → p∣n → IsSquare (a : ZMod p)) :
    IsSquare (a : ZMod n) := by
  induction n using _root_.induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0,Subsingleton.elim _ _⟩
  | prime_mul p n hp ih =>
    have hcop : p.Coprime n := by
      by_contra hc
      exact hp.not_isUnit (hn p <| mul_dvd_mul_left p <| hp.dvd_iff_not_coprime.mpr hc)
    apply square_mul a hcop
    · exact hlocal p hp (Nat.dvd_mul_right p n)
    · exact ih hn.of_mul_right (fun q hq hqn =>
        hlocal q hq (dvd_mul_of_dvd_right hqn p))

/-- A prime divisor of a squarefree signed coefficient occurs only once. -/
theorem prime_factor_once (b : ℤ) (hb : Squarefree b)
    (p : ℕ) (hp : p.Prime) (hpb : (p:ℤ)∣b) :
    ∃ B : ℤ, b=(p:ℤ)*B ∧ ¬(p:ℤ)∣B := by
  obtain ⟨B,hB⟩ := hpb
  refine ⟨B,hB,?_⟩
  intro hdiv
  apply (Int.squarefree_iff_prime_sq_not_dvd.mp hb p hp)
  obtain ⟨c,hc⟩ := hdiv
  refine ⟨c,?_⟩
  rw [hB,hc]
  ring

end LegendreSquarefreeCRT318
