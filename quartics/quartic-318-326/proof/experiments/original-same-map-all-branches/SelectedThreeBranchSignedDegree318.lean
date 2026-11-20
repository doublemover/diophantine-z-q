module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic
public section
noncomputable section

namespace SelectedThreeBranchSignedDegree318

section Sign
variable {A : Type*} [AddCommGroup A]

/-- Exactly one simultaneous sign is selected by any injective rank.
There is no independent sign on the prime factors of the level. -/
@[expose] def representatives (P : Finset A) (rank : A ↪ ℕ) : Finset A :=
  P.filter (fun a => rank a < rank (-a))

theorem twice_representatives (P : Finset A) (rank : A ↪ ℕ)
    (stable : ∀ a ∈ P, -a ∈ P) (free : ∀ a ∈ P, -a ≠ a) :
    2*(representatives P rank).card = P.card := by
  let other := P.filter (fun a => ¬rank a < rank (-a))
  have hCard : (representatives P rank).card = other.card := by
    apply Finset.card_nbij' (fun a : A => -a) (fun a : A => -a)
    · intro a ha
      change a ∈ P.filter (fun a => rank a < rank (-a)) at ha
      obtain ⟨ha,hlt⟩ := Finset.mem_filter.mp ha
      change -a ∈ P.filter (fun a => ¬rank a < rank (-a))
      refine Finset.mem_filter.mpr ⟨stable a ha,?_⟩
      simpa only [neg_neg] using (not_lt_of_ge hlt.le)
    · intro a ha
      change a ∈ P.filter (fun a => ¬rank a < rank (-a)) at ha
      obtain ⟨ha,hlt⟩ := Finset.mem_filter.mp ha
      change -a ∈ P.filter (fun a => rank a < rank (-a))
      refine Finset.mem_filter.mpr ⟨stable a ha,?_⟩
      have hne : rank (-a) ≠ rank a := fun h => free a ha (rank.injective h)
      simpa only [neg_neg] using lt_of_le_of_ne (le_of_not_gt hlt) hne
    · intro a _
      exact neg_neg a
    · intro a _
      exact neg_neg a
  have hSum : (representatives P rank).card + other.card = P.card :=
    Finset.card_filter_add_card_filter_not (s:=P) (fun a => rank a < rank (-a))
  omega

theorem no_fixed_sign {a : A} {M : ℕ} (ord : addOrderOf a = M) (hM : 2 < M) : -a ≠ a := by
  intro h
  have hz : 2 • a = 0 := by
    calc
      _ = a+a := two_nsmul a
      _ = a+(-a) := congrArg (fun z => a+z) h.symm
      _ = 0 := add_neg_cancel a
  have hd : M ∣ 2 := ord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  exact (not_le_of_gt hM) (Nat.le_of_dvd (by decide) hd)

end Sign

section Literal
variable (M : ℕ) [NeZero M]
abbrev V := ZMod M × ZMod M

@[expose] def primitive : Finset (V M) :=
  Finset.univ.filter (fun a => addOrderOf a = M)

theorem primitive_twice_bound (hM : 2 < M) (rank : V M ↪ ℕ) :
    2*(representatives (primitive M) rank).card ≤ M^2 := by
  have hs : ∀ a ∈ primitive M, -a ∈ primitive M := by
    intro a ha
    have h := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [addOrderOf_neg] using h⟩
  have hf : ∀ a ∈ primitive M, -a ≠ a := fun _ ha =>
    no_fixed_sign (Finset.mem_filter.mp ha).2 hM
  rw [twice_representatives (primitive M) rank hs hf]
  exact (Finset.card_le_univ (primitive M)).trans_eq (by simp [pow_two])

end Literal

section Elliptic
variable {R : Type*} [CommRing R]

@[expose] def S (a : R × R) : R × R := (-a.2,a.1)
@[expose] def U (a : R × R) : R × R := (-a.2,a.1+a.2)

theorem S_sq (a : R × R) : S (S a) = -a := by
  apply Prod.ext <;> simp [S]

theorem U_cube (a : R × R) : U (U (U a)) = -a := by
  apply Prod.ext <;> simp [U] <;> abel

/-- An elliptic generator fixing a signed class forces its underlying
vector to be killed by 2. This does not use parity of the level. -/
theorem S_fixed_kills (a : R × R) (h : S a = a ∨ S a = -a) : 2 • a = 0 := by
  rcases h with h|h
  · have h₁ : -a.2 = a.1 := congrArg Prod.fst h
    have h₂ : a.1 = a.2 := congrArg Prod.snd h
    apply Prod.ext
    · change (2:ℕ) • a.1 = 0
      rw [two_nsmul]
      linear_combination -h₁+h₂
    · change (2:ℕ) • a.2 = 0
      rw [two_nsmul]
      linear_combination -h₁-h₂
  · have h₁ : -a.2 = -a.1 := congrArg Prod.fst h
    have h₂ : a.1 = -a.2 := congrArg Prod.snd h
    apply Prod.ext
    · change (2:ℕ) • a.1 = 0
      rw [two_nsmul]
      linear_combination h₁+h₂
    · change (2:ℕ) • a.2 = 0
      rw [two_nsmul]
      linear_combination h₂-h₁

/-- The other elliptic generator forces signed-fixed vectors to be
killed by 3. Exact primitive level >3 excludes both fixed sets. -/
theorem U_fixed_kills (a : R × R) (h : U a = a ∨ U a = -a) : 3 • a = 0 := by
  rcases h with h|h
  · have h₁ : -a.2 = a.1 := congrArg Prod.fst h
    have h₂ : a.1+a.2 = a.2 := congrArg Prod.snd h
    apply Prod.ext
    · change (3:ℕ) • a.1 = 0
      rw [show (3:ℕ)=2+1 by decide,add_nsmul,two_nsmul,one_nsmul]
      linear_combination 3*h₂
    · change (3:ℕ) • a.2 = 0
      rw [show (3:ℕ)=2+1 by decide,add_nsmul,two_nsmul,one_nsmul]
      linear_combination -3*h₁-3*h₂
  · have h₁ : -a.2 = -a.1 := congrArg Prod.fst h
    have h₂ : a.1+a.2 = -a.2 := congrArg Prod.snd h
    apply Prod.ext
    · change (3:ℕ) • a.1 = 0
      rw [show (3:ℕ)=2+1 by decide,add_nsmul,two_nsmul,one_nsmul]
      linear_combination 2*h₁+h₂
    · change (3:ℕ) • a.2 = 0
      rw [show (3:ℕ)=2+1 by decide,add_nsmul,two_nsmul,one_nsmul]
      linear_combination -h₁+h₂

theorem no_signed_elliptic_fixed (a : R × R) {M : ℕ} (ord : addOrderOf a = M) (hM : 3 < M) :
    ¬(S a = a ∨ S a = -a) ∧ ¬(U a = a ∨ U a = -a) := by
  constructor
  · intro ha
    have hd : M ∣ 2 := ord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr (S_fixed_kills a ha)
    have h := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  · intro ha
    have hd : M ∣ 3 := ord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr (U_fixed_kills a ha)
    have h := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega

end Elliptic

/-- The same literal dj has orders 2 at the threefold elliptic fiber,
1 at the twofold elliptic fiber, and −e−1 at cusp width e. The
displayed degree identity is the honest remaining canonical-divisor
input; no genus/table assertion is supplied on an independent curve. -/
theorem bounded_genus {g d c0 c1728 cinf : ℕ} (hd : 0 < d)
    (atZero : 3*c0 = d) (at1728 : 2*c1728 = d) (cusp : 0 < cinf)
    (canonical : 2*(g:ℤ)-2 = 2*(c0:ℤ)+c1728-d-cinf) :
    12*g+6*cinf=d+12 ∧ 12*g≤d+6 ∧ 2*g-2<d := by
  omega

end SelectedThreeBranchSignedDegree318

#print axioms SelectedThreeBranchSignedDegree318.twice_representatives
#print axioms SelectedThreeBranchSignedDegree318.primitive_twice_bound
#print axioms SelectedThreeBranchSignedDegree318.no_signed_elliptic_fixed
#print axioms SelectedThreeBranchSignedDegree318.bounded_genus
