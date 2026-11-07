module
public import Height13RealLog
public section
namespace OrderSeparation

/-- A positive multiple below twice a positive divisor is exactly the divisor. -/
theorem small_multiple_eq (p d : ℕ) (_hp : 0<p) (hd : 0<d)
    (hbound : d<2*p) (hdiv : p∣d) : d=p := by
  obtain ⟨k,rfl⟩ := hdiv
  have hk0 : k≠0 := by intro hk; simp [hk] at hd
  have hk2 : k<2 := by
    by_contra hk
    have hh := Nat.mul_le_mul_left p (show 2≤k by omega)
    omega
  have hk : k=1 := by omega
  simp [hk]

/-- The off-diagonal part needs only spacing greater than the Hasse error. -/
theorem off_diagonal_not_dvd (p q d : ℕ) (E : ℝ)
    (_hp : 0<p) (hd : 0<d) (hbound : d<2*p)
    (hhasse : |(d:ℝ)-(q:ℝ)|≤E)
    (hspacing : E < |(p:ℝ)-(q:ℝ)|) : ¬p∣d := by
  intro hv
  have heq := small_multiple_eq p d _hp hd hbound hv
  rw [heq] at hhasse
  exact (not_lt_of_ge hhasse) hspacing

/-- At the same position, the even group order cannot equal the odd prime. -/
theorem diagonal_not_dvd (p d : ℕ) (_hp : 0<p) (hd : 0<d)
    (hbound : d<2*p) (hpodd : Odd p) (hdeven : Even d) : ¬p∣d := by
  intro hv
  have heq := small_multiple_eq p d _hp hd hbound hv
  rw [heq] at hdeven
  obtain ⟨a,ha⟩ := hpodd
  obtain ⟨b,hb⟩ := hdeven
  omega

/-- The entire finite selected family is separated from all opposite orders. -/
theorem family_not_dvd {ι : Type*} [DecidableEq ι] (p d : ι→ℕ) (E : ℝ)
    (hp : ∀i,0<p i) (hd : ∀i,0<d i)
    (hbound : ∀i j,d j<2*p i) (hpodd : ∀i,Odd (p i))
    (hdeven : ∀i,Even (d i))
    (hhasse : ∀i,|(d i:ℝ)-(p i:ℝ)|≤E)
    (hspacing : ∀i j,i≠j→E < |(p i:ℝ)-(p j:ℝ)|) :
    ∀i j,¬p i∣d j := by
  intro i j
  by_cases hij : i=j
  · subst j
    exact diagonal_not_dvd _ _ (hp i) (hd i) (hbound i i) (hpodd i) (hdeven i)
  · exact off_diagonal_not_dvd _ _ _ E (hp i) (hd j) (hbound i j)
      (hhasse j) (hspacing i j hij)

#print axioms family_not_dvd
end OrderSeparation
