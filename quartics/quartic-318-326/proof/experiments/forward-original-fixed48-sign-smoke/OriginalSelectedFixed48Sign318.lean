module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public section

namespace OriginalSelectedFixed48Sign318

/-- Original affine cubic; its three roots are 0, n, and -3n. -/
theorem literal_cubic {R : Type*} [CommRing R] (n x : R) :
    x * (x - n) * (x + 3*n) = x^3 + 2*n*x^2 - 3*n^2*x := by ring

/-- Martin–Ono's conductor 48 row, with x_old=u+1 and y unchanged. -/
theorem fixed48_model {R : Type*} [CommRing R] (u : R) :
    (u + 1) * ((u + 1) - (-1)) * ((u + 1) + 3*(-1)) =
      u^3 + u^2 - 4*u - 4 := by ring

/-- If a² = D then scaling (x,y) by (D,a³) is the literal twist from
E_{-1} to E_{-D}. Changing a to -a changes only the ordinate sign. -/
theorem scale_from_minus_one {R : Type*} [CommRing R] (D a x y : R)
    (ha : a^2 = D) (hxy : y^2 = x*(x-(-1))*(x+3*(-1))) :
    (a^3*y)^2 = (D*x)*((D*x)-(-D))*((D*x)+3*(-D)) := by
  calc
    (a^3*y)^2 = (a^2)^3 * y^2 := by ring
    _ = (D*x)*((D*x)-(-D))*((D*x)+3*(-D)) := by rw [ha,hxy]; ring

private theorem mod12_eq (n : ℕ) (hr : (n : ZMod 12) = 11) : n % 12 = 11 := by
  have h := congrArg ZMod.val hr
  norm_num only [ZMod.val_natCast] at h
  exact h

private theorem coprime96 (n : ℕ) (hr : n % 12 = 11) : n.Coprime 96 := by
  have hf : ∀ a : Fin 96, a.val % 12 = 11 → a.val.Coprime 96 := by decide
  have hm : (n % 96) % 12 = 11 :=
    (Nat.mod_mod_of_dvd n (by decide : 12 ∣ 96)).trans hr
  exact (ZMod.coprime_mod_iff_coprime n 96).mp
    (hf ⟨n % 96, Nat.mod_lt n (by decide)⟩ hm)

/-- Exact guards for the odd fundamental-discriminant criterion and
the conductor-coprime twist formula (the latter requires gcd(D,2*48)=1). -/
theorem twist_guards (n : ℕ) (hp : 0 < n) (hs : Squarefree n)
    (hr : (n : ZMod 12) = 11) :
    -(n : ℤ) < 0 ∧ Squarefree (-(n : ℤ)).natAbs ∧
      (-(n : ℤ)) % 4 = 1 ∧ (-(n : ℤ)).natAbs.Coprime 96 := by
  have hpZ : 0 < (n : ℤ) := by exact_mod_cast hp
  have hrN := mod12_eq n hr
  have hrZ : (n : ℤ) % 12 = 11 := by
    simpa only [Int.natCast_emod] using congrArg (fun m : ℕ => (m : ℤ)) hrN
  refine ⟨by omega, ?_, by omega, ?_⟩
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hs
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using coprime96 n hrN

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The three factors of Kronecker χ_D(-48)=χ_D(-1) χ_D(2)^4 χ_D(3):
the sign of D, the exact pinned mod-eight quadratic character, and the
Legendre symbol modulo three. The global twist equation is separate. -/
@[expose] def conductor48Factor (D : ℤ) : ℤ :=
  (if D < 0 then -1 else 1) * (ZMod.χ₈ (D : ZMod 8))^4 * legendreSym 3 D

theorem conductor48Factor_selected (n : ℕ) (hp : 0 < n)
    (hr : (n : ZMod 12) = 11) : conductor48Factor (-(n : ℤ)) = -1 := by
  have hpZ : 0 < (n : ℤ) := by exact_mod_cast hp
  have hrN := mod12_eq n hr
  have hrZ : (n : ℤ) % 12 = 11 := by
    simpa only [Int.natCast_emod] using congrArg (fun m : ℕ => (m : ℤ)) hrN
  have hodd : (-(n : ℤ)) % 2 ≠ 0 := by omega
  have h3 : (-(n : ℤ)) % (3 : ℤ) = 1 := by omega
  have hleg : legendreSym 3 (-(n : ℤ)) = 1 := by
    rw [legendreSym.mod 3 (-(n : ℤ)), h3, legendreSym.at_one]
  rw [conductor48Factor, if_pos (by omega : -(n : ℤ) < 0), hleg,
    ZMod.χ₈_int_eq_if_mod_eight, if_neg hodd]
  split <;> norm_num

/-- Only an arithmetic boundary: W must be the analytic root number
of the literal E_n and w48 that of the literal E_{-1}. Martin–Ono plus
the eta inversion gives w48=1; the coprime quadratic twist theorem gives
the displayed equation. No parity, rank, or Selmer premise. -/
@[expose] def CoprimeRootEquation (W : ℕ → ℤ) (w48 : ℤ) : Prop :=
  ∀ n : ℕ, let D := -(n : ℤ)
    D < 0 → Squarefree D.natAbs → D % 4 = 1 → D.natAbs.Coprime 96 →
      W n = w48 * conductor48Factor D

theorem selected_sign_negative (W : ℕ → ℤ) (w48 : ℤ)
    (hbase : w48 = 1) (htwist : CoprimeRootEquation W w48)
    (n : ℕ) (hp : 0 < n) (hs : Squarefree n) (hr : (n : ZMod 12) = 11) :
    W n = -1 := by
  obtain ⟨hD,hDsf,hD4,hcp⟩ := twist_guards n hp hs hr
  calc
    W n = w48 * conductor48Factor (-(n : ℤ)) := htwist n hD hDsf hD4 hcp
    _ = -1 := by rw [hbase, conductor48Factor_selected n hp hr, one_mul]

end OriginalSelectedFixed48Sign318

#print axioms OriginalSelectedFixed48Sign318.twist_guards
#print axioms OriginalSelectedFixed48Sign318.selected_sign_negative
