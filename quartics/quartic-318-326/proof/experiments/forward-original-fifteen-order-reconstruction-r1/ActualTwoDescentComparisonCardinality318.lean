module
public import ActualTwoDescentLocalClassification318
public import Mathlib.SetTheory.Cardinal.Finite
public section
noncomputable section
namespace ActualTwoDescentComparisonCardinality318
open ActualTwoDescentLocalClassification318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentPrimeMonomials318
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

abbrev ComparisonSpace (p : Option U → ℕ) :=
  {x : ZMod 2 × (Option U → ZMod 2) × (Option U → ZMod 2) // Admissible p x.1 x.2.1 x.2.2}

/-- A genuine equivalence, not merely an upper bound or assumed rank.
The two coordinates are the surviving torsion and beta coefficients. -/
def actual_comparison_equiv (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1) :
    (ZMod 2 × ZMod 2) ≃ ComparisonSpace p := by
  let f : (ZMod 2 × ZMod 2) → ComparisonSpace p := fun ce =>
    ⟨(0,ce.1 • ones (Option U)+ce.2 • beta,0),
      (actual_local_classification p hp2 hp3 a beta N C _ _ _).mpr ⟨rfl,rfl,ce.1,ce.2,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro ce de h
    have hv := congrArg (fun x : ComparisonSpace p => x.val.2.1) h
    obtain ⟨h1,h2⟩ := actual_class_coefficients_unique beta h0 b hb ce.1 ce.2 de.1 de.2 hv
    exact Prod.ext h1 h2
  · rintro ⟨⟨δ,u,v⟩,H⟩
    obtain ⟨rfl,rfl,c,e,rfl⟩ := (actual_local_classification p hp2 hp3 a beta N C δ u v).mp H
    exact ⟨(c,e),Subtype.ext rfl⟩

/-- Exactly four actual comparison classes, before the second-coordinate
sign normalization. This does not identify an elliptic Selmer group. -/
theorem actual_comparison_card (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1) :
    Nat.card (ComparisonSpace p)=4 := by
  rw [←Nat.card_congr (actual_comparison_equiv p hp2 hp3 a beta N C h0 b hb)]
  norm_num [Nat.card_eq_fintype_card]

/-- The four representatives remain distinct as ACTUAL rational
squareclasses, rather than just distinct coefficient vectors. -/
theorem actual_four_squareclasses_distinct (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (beta : Option U → ZMod 2)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1)
    (c e c' e' : ZMod 2) (r : ℚ) (hr : r ≠ 0)
    (he : (monomial p (c • ones (Option U)+e • beta) : ℚ)=
      (monomial p (c' • ones (Option U)+e' • beta) : ℚ)*r^2) :
    c=c' ∧ e=e' :=
  actual_class_coefficients_unique beta h0 b hb c e c' e'
    (actual_monomial_squareclass_injective p hd _ _ r hr he)

end ActualTwoDescentComparisonCardinality318
