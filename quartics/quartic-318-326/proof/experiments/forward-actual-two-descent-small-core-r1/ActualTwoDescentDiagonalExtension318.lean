module
public import ActualTwoDescentCore318
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public section
noncomputable section
namespace ActualTwoDescentDiagonalExtension318
open scoped Matrix
set_option maxHeartbeats 16000000

/-- An ordered finite enlargement of the ORIGINAL core index set.
No core row is deleted when the second-twist support is adjoined. -/
@[expose] def Index (U : Type*) : ℕ → Type _
  | 0 => U
  | n+1 => Index U n ⊕ Unit

instance indexFintype (U : Type*) [Fintype U] : (n : ℕ) → Fintype (Index U n)
  | 0 => inferInstanceAs (Fintype U)
  | n+1 => letI := indexFintype U n; inferInstanceAs (Fintype (Index U n ⊕ Unit))

instance indexDecidableEq (U : Type*) [DecidableEq U] : (n : ℕ) → DecidableEq (Index U n)
  | 0 => inferInstanceAs (DecidableEq U)
  | n+1 => letI := indexDecidableEq U n; inferInstanceAs (DecidableEq (Index U n ⊕ Unit))

@[expose] def baseEmbed (U : Type*) : (n : ℕ) → U → Index U n
  | 0 => id
  | n+1 => Sum.inl ∘ baseEmbed U n

/-- One actual Schur-complement step chooses only the new diagonal.
All previously prescribed row and column symbols remain untouched. -/
lemma actual_one_step {U : Type*} [Fintype U] [DecidableEq U]
    (A : Matrix U U (ZMod 2)) (hA : IsUnit A)
    (B : Matrix U Unit (ZMod 2)) (C : Matrix Unit U (ZMod 2)) :
    IsUnit (Matrix.fromBlocks A B C (C*A⁻¹*B+1)) := by
  letI : Invertible A := hA.nonempty_invertible.some
  apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
  rw [Matrix.invOf_eq_nonsing_inv,add_sub_cancel_left]
  exact isUnit_one

/-- Every finite second-support enlargement admits diagonal choices
that preserve the entire nonsingular core AND every off-diagonal symbol.
This constructs the simultaneous choice used in the retained two-descent
argument, not merely separate nonsingularity on unrelated matrices. -/
theorem actual_diagonal_extension {U : Type*} [Fintype U] [DecidableEq U] :
    ∀ (n : ℕ) (M : Matrix (Index U n) (Index U n) (ZMod 2)),
      IsUnit (M.submatrix (baseEmbed U n) (baseEmbed U n)) →
      ∃ M' : Matrix (Index U n) (Index U n) (ZMod 2), IsUnit M' ∧
        (∀ i j, i ≠ j → M' i j=M i j) ∧
        (∀ i j : U, M' (baseEmbed U n i) (baseEmbed U n j)=
          M (baseEmbed U n i) (baseEmbed U n j)) := by
  intro n
  induction n with
  | zero =>
    intro M hM
    refine ⟨M,?_,fun _ _ _ => rfl,fun _ _ => rfl⟩
    change IsUnit M at hM
    exact hM
  | succ n ih =>
    intro M hM
    let A := M.toBlocks₁₁
    let B := M.toBlocks₁₂
    let C := M.toBlocks₂₁
    have hA : IsUnit (A.submatrix (baseEmbed U n) (baseEmbed U n)) := hM
    obtain ⟨A',hA',hoff,hbase⟩ := ih A hA
    refine ⟨Matrix.fromBlocks A' B C (C*A'⁻¹*B+1),actual_one_step A' hA' B C,?_,?_⟩
    · intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hoff i j (fun he => hij (congrArg Sum.inl he))
        | inr j => rfl
      | inr i =>
        cases j with
        | inl j => rfl
        | inr j => exact False.elim (hij (congrArg Sum.inr (Subsingleton.elim i j)))
    · intro i j
      exact hbase i j

/-- The constructed modification is literally a diagonal bit toggle,
zero on every original support entry, rather than a changed symbol matrix. -/
theorem actual_diagonal_toggle {U : Type*} [Fintype U] [DecidableEq U]
    (n : ℕ) (M : Matrix (Index U n) (Index U n) (ZMod 2))
    (hM : IsUnit (M.submatrix (baseEmbed U n) (baseEmbed U n))) :
    ∃ t : Index U n → ZMod 2, (∀ i : U, t (baseEmbed U n i)=0) ∧
      IsUnit (M+Matrix.diagonal t) := by
  obtain ⟨M',hM',hoff,hbase⟩ := actual_diagonal_extension n M hM
  let t : Index U n → ZMod 2 := fun i => M' i i-M i i
  refine ⟨t,fun i => by dsimp [t]; rw [hbase,sub_self],?_⟩
  have he : M+Matrix.diagonal t=M' := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [t]
    · simp [Matrix.diagonal,hij,hoff i j hij]
  rw [he]
  exact hM'

end ActualTwoDescentDiagonalExtension318
