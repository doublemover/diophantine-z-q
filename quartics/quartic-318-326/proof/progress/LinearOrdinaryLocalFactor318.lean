module
public import Mathlib.Tactic
public section
noncomputable section
namespace LinearOrdinaryLocalFactor318
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The denominator form contributes its own zero line q=0. Merged slopes
are actual residues in K, so small primes with colliding slopes are not
incorrectly counted using their characteristic-zero cardinality. -/
def unitRows (S : Finset K) :=
  {x : K × K // x.2 ≠ 0 ∧ ∀ k ∈ S, x.1 + k*x.2 ≠ 0}

/-- At q≠0, t=−u/q sees every slope obstruction exactly once. -/
def unitEquiv (S : Finset K) : unitRows S ≃
    (↑(({0}:Finset K)ᶜ) × ↑(Sᶜ)) where
  toFun x := by
    let t := -x.val.1/x.val.2
    have ht : t ∉ S := by
      intro h
      apply x.property.2 t h
      dsimp [t]
      field_simp [x.property.1]
      ring
    exact (⟨x.val.2,by simpa using x.property.1⟩,⟨t,by simpa using ht⟩)
  invFun z := by
    let q := z.1.val
    let t := z.2.val
    have hq : q ≠ 0 := fun h => (Finset.mem_compl.mp z.1.property) (Finset.mem_singleton.mpr h)
    have ht : t ∉ S := Finset.mem_compl.mp z.2.property
    refine ⟨(-t*q,q),hq,?_⟩
    intro k hk he
    change -t*q+k*q=0 at he
    have eq : (k-t)*q=0 := by linear_combination he
    exact ht ((sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right hq)) ▸ hk)
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change -(-x.val.1/x.val.2)*x.val.2=x.val.1
      field_simp [x.property.1]
    · rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change -(-(z.2.val)*z.1.val)/z.1.val=z.2.val
      have hq : z.1.val ≠ 0 := fun h =>
        (Finset.mem_compl.mp z.1.property) (Finset.mem_singleton.mpr h)
      field_simp [hq]

/-- Exact ordinary finite-field numerator: (p−1)(p−m), with m the number
of distinct contact slope residues and one additional order-only q form. -/
theorem unit_count (S : Finset K) [Fintype (unitRows S)] :
    Fintype.card (unitRows S) =
      (Fintype.card K-1)*(Fintype.card K-S.card) := by
  rw [Fintype.card_congr (unitEquiv S)]
  simp [Fintype.card_prod]

/-- The observed ordinary Euler factor when r=m+1 is
1-r/p+(r-1)/p², a loss of no spurious Gaussian multiplicity. -/
theorem unit_probability (p m : ℝ) (hp : p ≠ 0) :
    ((p-1)*(p-m))/p^2 = 1-(m+1)/p+m/p^2 := by
  field_simp [hp]
  ring

/-- At the fixed base abelian conductor, Q=0 in its residue ring. Using
the prescribed diagonal unit grid cell (b,b), *all* forms equal b; taking
q=0 instead would lose the denominator prime's local unit condition. -/
theorem diagonal_cell {R : Type*} [CommRing R] (Q b : R) (hQ : Q=0) :
    (∀ k : R, b+k*Q^2*b=b) ∧ (IsUnit b → ∀ k : R, IsUnit (b+k*Q^2*b)) := by
  subst Q
  simp

end LinearOrdinaryLocalFactor318
