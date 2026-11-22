module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Tactic

/-! Sign, two, and odd prime columns of rational quadratic reciprocity.
The proof works with an arbitrary finite set of odd primes, including the empty
set. It uses actual quadratic reciprocity at distinct odd primes. This is a
matrix of local squareclass coordinates, not a postulated global symbol law. -/
public section
noncomputable section
namespace RationalHilbertPrimeBasis318
open scoped BigOperators

abbrev B := ZMod 2
abbrev Key (I : Type*) := Option (Option I)
-- none = -1, some none = 2, some (some i) = positive odd prime pᵢ.

structure Primes (I : Type*) where
  p : I → ℕ
  prime : ∀ i, (p i).Prime
  odd : ∀ i, p i ≠ 2
  distinct : Function.Injective p

def eps (p : ℕ) : B := if p % 4 = 3 then 1 else 0
def oct (p : ℕ) : B := if p % 8 = 1 ∨ p % 8 = 7 then 0 else 1

def nsq {p : ℕ} (u : ZMod p) : B := by
  classical
  exact if IsSquare u then 0 else 1

theorem minus_bit (p : ℕ) [Fact p.Prime] : nsq (-1 : ZMod p) = eps p := by
  classical
  by_cases h : p % 4 = 3 <;> simp [nsq, eps, ZMod.exists_sq_eq_neg_one_iff, h]

theorem two_bit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    nsq (2 : ZMod p) = oct p := by
  classical
  simp [nsq, oct, ZMod.exists_sq_eq_two_iff hp]

private theorem odd_mod_four {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have h := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp
  omega

/-- Additive quadratic reciprocity, including both supplement signs. The two
arguments are primes themselves, not residue-field labels chosen for a test. -/
theorem odd_bit_swap (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    nsq (q : ZMod p) + nsq (p : ZMod q) = eps p * eps q := by
  classical
  rcases odd_mod_four hp with hp1 | hp3
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp1 hq
    have hn : p % 4 ≠ 3 := by omega
    by_cases hs : IsSquare (q : ZMod p)
    · simp [nsq, eps, hs, h.mp hs, hn]
    · have ht : ¬ IsSquare (p : ZMod q) := fun hq => hs (h.mpr hq)
      simp [nsq, eps, hs, ht, hn]
      decide
  · rcases odd_mod_four hq with hq1 | hq3
    · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hq1 hp
      have hn : q % 4 ≠ 3 := by omega
      by_cases hs : IsSquare (p : ZMod q)
      · simp [nsq, eps, hs, h.mp hs, hn]
      · have ht : ¬ IsSquare (q : ZMod p) := fun hq => hs (h.mpr hq)
        simp [nsq, eps, hs, ht, hn]
        decide
    · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp3 hq3 hpq
      by_cases hs : IsSquare (q : ZMod p)
      · simp [nsq, eps, hs, h.mp hs, hp3, hq3]
      · have ht : IsSquare (p : ZMod q) := by
          by_contra hn
          exact hs (h.mpr hn)
        simp [nsq, eps, hs, ht, hp3, hq3]

lemma bit_double (x : B) : x + x = 0 := by fin_cases x <;> decide
lemma bit_square : ∀ x : ZMod 2, x * x = x := by decide

inductive Slot (I : Type*) where
  | realSign | dyEps | dyVal | dyOct | oddVal (i : I) | oddUnit (i : I)
  deriving DecidableEq, Fintype

abbrev Local (I : Type*) := Slot I → B
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Actual columns in the ordered coordinates (sign; ε₂, v₂, ω₂;
vₚ, nonsquare residue of the p-adic unit). No Legendre symbol at zero:
the unit of p in its own uniformizer column is one. -/
def column (P : Primes I) : Key I → Local I
  | none, .realSign => 1
  | none, .dyEps => 1
  | none, .oddUnit i => eps (P.p i)
  | some none, .dyVal => 1
  | some none, .oddUnit i => oct (P.p i)
  | some (some j), .dyEps => eps (P.p j)
  | some (some j), .dyOct => oct (P.p j)
  | some (some j), .oddVal i => if i = j then 1 else 0
  | some (some j), .oddUnit i =>
      if i = j then 0 else nsq (P.p j : ZMod (P.p i))
  | _, _ => 0

/-- Sum of the scalar local Hilbert-coordinate formulas. The odd self-term
εₚ vₚ(x)vₚ(y) and dyadic ε₂(x)ε₂(y) cannot both be discarded. -/
def symbol (P : Primes I) (x y : Local I) : B :=
  x .realSign * y .realSign + x .dyEps * y .dyEps +
  x .dyVal * y .dyOct + x .dyOct * y .dyVal +
  (∑ i, eps (P.p i) * x (.oddVal i) * y (.oddVal i)) +
  (∑ i, x (.oddUnit i) * y (.oddVal i)) +
  (∑ i, x (.oddVal i) * y (.oddUnit i))

omit [DecidableEq I] in
theorem symbol_symm (P : Primes I) (x y : Local I) : symbol P x y = symbol P y x := by
  simp only [symbol, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]

omit [DecidableEq I] in
lemma symbol_add_left (P : Primes I) (x y z : Local I) :
    symbol P (x+y) z = symbol P x z + symbol P y z := by
  simp only [symbol, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  abel

omit [DecidableEq I] in
lemma symbol_smul_left (P : Primes I) (r : B) (x y : Local I) :
    symbol P (r • x) y = r * symbol P x y := by
  have h01 : ∀ t : B, t = 0 ∨ t = 1 := by decide
  rcases h01 r with rfl | rfl
  · rw [zero_smul, zero_mul]
    simp [symbol]
  · rw [one_smul, one_mul]

omit [DecidableEq I] in
lemma symbol_sum_left {J : Type*} (P : Primes I) (s : Finset J) (x : J → Local I)
    (y : Local I) : symbol P (∑ j ∈ s, x j) y = ∑ j ∈ s, symbol P (x j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symbol]
  | insert a s ha ih => simp [Finset.sum_insert, ha, symbol_add_left, ih]

private theorem col_neg_left (P : Primes I) (a : Key I) :
    symbol P (column P none) (column P a) = 0 := by
  rcases a with _ | (_ | i)
  · simp [symbol, column]
    decide
  · simp [symbol, column]
  · simp [symbol, column, mul_ite, bit_double]

private theorem col_two_left (P : Primes I) (a : Key I) :
    symbol P (column P (some none)) (column P a) = 0 := by
  rcases a with _ | (_ | i)
  · simp [symbol, column]
  · simp [symbol, column]
  · simp [symbol, column, mul_ite, bit_double]

private theorem col_odd_pair (P : Primes I) (j k : I) :
    symbol P (column P (some (some j))) (column P (some (some k))) = 0 := by
  classical
  have pick (a b : I) (f : I → B) :
      (∑ i : I, if i = a then 0 else if i = b then f i else 0) =
        if b = a then 0 else f b := by
    calc
      _ = (if b = a then 0 else if b = b then f b else 0) :=
        Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)
      _ = _ := by simp
  by_cases h : j = k
  · subst k
    simp [symbol, column, mul_ite, ite_mul, bit_square, bit_double]
    rw [pick, ite_eq_left rfl]
  · let : Fact (P.p j).Prime := ⟨P.prime j⟩
    let : Fact (P.p k).Prime := ⟨P.prime k⟩
    have hr := odd_bit_swap (P.p j) (P.p k) (P.odd j) (P.odd k) (fun he => h (P.distinct he))
    calc
      _ = eps (P.p j) * eps (P.p k) +
        (nsq (P.p k : ZMod (P.p j)) + nsq (P.p j : ZMod (P.p k))) := by
          simp [symbol, column, mul_ite, ite_mul, Ne.symm h]
          rw [pick, ite_eq_right h]
          abel
      _ = 0 := by rw [hr, bit_double]

/-- All generator pairs, with no extra reciprocity oracle. -/
theorem column_reciprocity (P : Primes I) (a b : Key I) :
    symbol P (column P a) (column P b) = 0 := by
  rcases a with _ | (_ | j)
  · exact col_neg_left P b
  · exact col_two_left P b
  · rcases b with _ | (_ | k)
    · exact (symbol_symm P _ _).trans (col_neg_left P _)
    · exact (symbol_symm P _ _).trans (col_two_left P _)
    · exact col_odd_pair P j k

def loc (P : Primes I) (g : Key I → B) : Local I :=
  ∑ a, (g a) • column P a

theorem symbol_loc_left (P : Primes I) (g : Key I → B) (y : Local I) :
    symbol P (loc P g) y = ∑ a, g a * symbol P (column P a) y := by
  unfold loc
  rw [symbol_sum_left]
  simp only [symbol_smul_left]

theorem column_loc (P : Primes I) (a : Key I) (g : Key I → B) :
    symbol P (column P a) (loc P g) = 0 := by
  rw [symbol_symm, symbol_loc_left]
  simp [column_reciprocity]

/-- Quadratic reciprocity on ALL products of the rational S-unit generators. -/
theorem loc_isotropic (P : Primes I) (g h : Key I → B) :
    symbol P (loc P g) (loc P h) = 0 := by
  rw [symbol_loc_left]
  simp [column_loc]

def pivot (x : Local I) : Key I → B
  | none => x .realSign
  | some none => x .dyVal
  | some (some i) => x (.oddVal i)

omit [Fintype I] in
lemma column_pivot (P : Primes I) (a b : Key I) :
    pivot (column P a) b = if b = a then 1 else 0 := by
  rcases a with _ | (_ | i) <;> rcases b with _ | (_ | j) <;>
    simp [pivot, column]

theorem pivot_loc (P : Primes I) (g : Key I → B) : pivot (loc P g) = g := by
  classical
  funext b
  have H (r : Slot I) : loc P g r = ∑ a, g a * column P a r := by
    simp [loc, Finset.sum_apply]
  have hb : pivot (loc P g) b = ∑ a, g a * pivot (column P a) b := by
    rcases b with _ | (_ | j) <;> simpa only [pivot] using H _
  simp [hb, column_pivot, mul_ite]

theorem loc_injective (P : Primes I) : Function.Injective (loc P) :=
  fun g h e => (pivot_loc P g).symm.trans ((congrArg pivot e).trans (pivot_loc P h))

/-- Exact converse, without a dimension count: the pivot-free residual
orthogonal to the three types of column must vanish. -/
theorem pivot_zero_orthogonal_zero (P : Primes I) (r : Local I)
    (hp : pivot r = 0) (hh : ∀ a : Key I, symbol P r (column P a) = 0) : r = 0 := by
  have hre : r .realSign = 0 := congrFun hp none
  have hv : r .dyVal = 0 := congrFun hp (some none)
  have hvp (j : I) : r (.oddVal j) = 0 := congrFun hp (some (some j))
  have he : r .dyEps = 0 := by simpa [symbol, column, hre, hv, hvp] using hh none
  have ho : r .dyOct = 0 := by simpa [symbol, column, hre, hv, hvp] using hh (some none)
  have hu (j : I) : r (.oddUnit j) = 0 := by
    simpa [symbol, column, hre, hv, hvp, he, ho, mul_ite] using hh (some (some j))
  funext s
  cases s <;> simp [hre, he, hv, ho, hvp, hu]

/-- Orthogonality to the global columns recovers the UNIQUE global word
directly from sign and finite valuation bits. -/
theorem orthogonal_iff_reconstructed (P : Primes I) (x : Local I) :
    (∀ a : Key I, symbol P x (column P a) = 0) ↔ x = loc P (pivot x) := by
  constructor
  · intro h
    let r := x + loc P (pivot x)
    have hp : pivot r = 0 := by
      funext k
      calc
        pivot r k = pivot x k + pivot (loc P (pivot x)) k := by
          rcases k with _ | (_ | j) <;> rfl
        _ = 0 := by rw [congrFun (pivot_loc P (pivot x)) k, bit_double]
    have hh (a : Key I) : symbol P r (column P a) = 0 := by
      rw [show r = x + loc P (pivot x) from rfl, symbol_add_left, h, zero_add,
        symbol_loc_left]
      simp [column_reciprocity]
    have hr := pivot_zero_orthogonal_zero P r hp hh
    funext s
    have e : x s + loc P (pivot x) s = 0 := congrFun hr s
    have ht := bit_double (loc P (pivot x) s)
    exact add_right_cancel (e.trans ht.symm)
  · intro h a
    calc
      symbol P x (column P a) = symbol P (loc P (pivot x)) (column P a) :=
        congrArg (fun t => symbol P t (column P a)) h
      _ = 0 := (symbol_symm P _ _).trans (column_loc P a _)

def cross (P : Primes I) (x y : Local I × Local I) : B :=
  symbol P x.1 y.2 + symbol P x.2 y.1

omit [DecidableEq I] in
lemma cross_alt (P : Primes I) (x : Local I × Local I) : cross P x x = 0 := by
  rw [cross, symbol_symm P x.2 x.1, bit_double]

/-- Self-annihilation AND maximality of the two-coordinate global image.
No nondegeneracy or global Hilbert reciprocity hypotheses in this receiver. -/
theorem cross_orthogonal_iff_global (P : Primes I) (x : Local I × Local I) :
    (∀ g h : Key I → B, cross P x (loc P g, loc P h) = 0) ↔
    x.1 = loc P (pivot x.1) ∧ x.2 = loc P (pivot x.2) := by
  classical
  have hl0 : loc P (0 : Key I → B) = 0 := by simp [loc]
  let oneCol (a : Key I) : Key I → B := fun b => if b = a then 1 else 0
  have hcol (a : Key I) : loc P (oneCol a) = column P a := by
    simp [loc, oneCol, ite_smul]
  constructor
  · intro H
    constructor
    · apply (orthogonal_iff_reconstructed P x.1).mp
      intro a
      simpa [cross, hl0, hcol, symbol] using H 0 (oneCol a)
    · apply (orthogonal_iff_reconstructed P x.2).mp
      intro a
      simpa [cross, hl0, hcol, symbol] using H (oneCol a) 0
  · rintro ⟨h1,h2⟩ g h
    change symbol P x.1 (loc P h) + symbol P x.2 (loc P g) = 0
    rw [h1, h2, loc_isotropic, loc_isotropic, add_zero]

end RationalHilbertPrimeBasis318
