module
public import OddAffineInput
public import NestedInput
public section
namespace ArithmeticSeparation

/-- A concrete arithmetic certificate still to be derived from the global
elliptic, local-congruence and height arguments. No existence is asserted here. -/
structure LabelSeparation (beta : ℚ) where
  label : ℤ
  modulus : ℕ
  divides : (modulus : ℤ) ∣ (beta-label).num
  small : (beta-label).num.natAbs < modulus

structure OddLabelSeparation (beta : ℚ) extends LabelSeparation beta where
  odd : Odd label

theorem label_eq {beta : ℚ} (c : LabelSeparation beta) : beta=c.label := by
  have hn : (beta-c.label).num=0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs c.divides (by simpa using c.small)
  exact sub_eq_zero.mp (Rat.num_eq_zero.mp hn)

theorem odd_affine_input (q : ℚ)
    (c : OddLabelSeparation (3723*(2*q+1)^2)) : ∃ z : ℤ, (z : ℚ)=q := by
  apply (OddAffineInput.odd_input_3723 q).mp
  exact ⟨c.label,c.odd,label_eq c.toLabelSeparation⟩

theorem nested_square_input (q : ℚ)
    (c : LabelSeparation ((102*q^2+357)^2)) : ∃ z : ℤ, (z : ℚ)=q := by
  apply (NestedInput.input_102_357_square_integral q).mp
  exact ⟨c.label,label_eq c⟩

/-- The two global arithmetic obligations are explicit parameters. This theorem
proves the final arithmetic deduction and transfers it through an already
proved whole-polynomial/source equivalence; it does not construct certificates. -/
theorem characterize_from_odd_certificates {W : Type*}
    (P : ℚ → W → ℚ) (Source : ℚ → Prop)
    (polynomial_source : ∀ q, (∃ w, P q w=0) ↔ Source q)
    (separation : ∀ q, Source q → Nonempty (OddLabelSeparation (3723*(2*q+1)^2)))
    (completeness : ∀ z : ℤ, Source z) :
    ∀ q, (∃ w, P q w=0) ↔ ∃ z : ℤ, (z : ℚ)=q := by
  intro q
  rw [polynomial_source]
  constructor
  · intro hs
    obtain ⟨certificate⟩ := separation q hs
    exact odd_affine_input q certificate
  · rintro ⟨z,rfl⟩
    exact completeness z

theorem characterize_from_nested_certificates {W : Type*}
    (P : ℚ → W → ℚ) (Source : ℚ → Prop)
    (polynomial_source : ∀ q, (∃ w, P q w=0) ↔ Source q)
    (separation : ∀ q, Source q → Nonempty (LabelSeparation ((102*q^2+357)^2)))
    (completeness : ∀ z : ℤ, Source z) :
    ∀ q, (∃ w, P q w=0) ↔ ∃ z : ℤ, (z : ℚ)=q := by
  intro q
  rw [polynomial_source]
  constructor
  · intro hs
    obtain ⟨certificate⟩ := separation q hs
    exact nested_square_input q certificate
  · rintro ⟨z,rfl⟩
    exact completeness z

end ArithmeticSeparation
