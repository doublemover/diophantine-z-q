module
public import ActualSourceHOneSmallPoles318
public import SourceCharacterFields318
public import Mathlib.Tactic.NormNum

public section
namespace SourceHOneCharacterIndices318
open ActualSourceHOneSmallPoles318
open scoped BigOperators
abbrev Index := Option (Fin 4)

/-- Literal correspondence: omitted-root characters first, full character last. -/
@[expose] def smallIndex : Index → SmallIndex
  | none => ⟨((1,(1,1)),2),by decide⟩
  | some i => ![⟨((1,(1,1)),1),by decide⟩,
      ⟨((0,(1,1)),1),by decide⟩,
      ⟨((1,(0,1)),1),by decide⟩,
      ⟨((1,(1,0)),1),by decide⟩] i

theorem smallIndex_bijective : Function.Bijective smallIndex := by decide

@[expose] def support : Index → Finset (Fin 4)
  | none => Finset.univ
  | some i => SourceCharacterFields318.complement i

@[expose] def epsilon (i : Index) (b : Fin 4 → Bool) : ℚ :=
  ∏ j ∈ support i, if b j then -1 else 1

/-- The same finite signs, evaluated in integers before the original rational cast. -/
@[expose] def epsilonInt (i : Index) (b : Fin 4 → Bool) : ℤ :=
  ∏ j ∈ support i, if b j then -1 else 1

lemma epsilonInt_cast (i : Index) (b : Fin 4 → Bool) :
    (epsilonInt i b : ℚ) = epsilon i b := by
  simp [epsilonInt, epsilon]

lemma epsilonInt_square : ∀ (i : Index) (b : Fin 4 → Bool), epsilonInt i b ^ 2 = 1 := by
  unfold epsilonInt support SourceCharacterFields318.complement
  decide

lemma epsilonInt_separates : ∀ i j : Index, i ≠ j →
    ∃ b : Fin 4 → Bool, epsilonInt i b = 1 ∧ epsilonInt j b = -1 := by
  unfold epsilonInt support SourceCharacterFields318.complement
  decide

lemma epsilonInt_orthogonality : ∀ i j : Index,
    (∑ b : Fin 4 → Bool, epsilonInt i b * epsilonInt j b) = if i = j then 16 else 0 := by
  unfold epsilonInt support SourceCharacterFields318.complement
  decide

theorem epsilon_square (i : Index) (b : Fin 4 → Bool) : epsilon i b ^ 2 = 1 := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (epsilonInt_square i b)
  simpa only [Int.cast_pow, Int.cast_one, epsilonInt_cast] using h

theorem epsilon_separates : ∀ i j : Index, i ≠ j →
    ∃ b : Fin 4 → Bool, epsilon i b = 1 ∧ epsilon j b = -1 := by
  intro i j hij
  obtain ⟨b,hi,hj⟩ := epsilonInt_separates i j hij
  refine ⟨b, ?_, ?_⟩
  · simpa only [epsilonInt_cast, Int.cast_one] using congrArg (fun z : ℤ => (z : ℚ)) hi
  · simpa only [epsilonInt_cast, Int.cast_neg, Int.cast_one] using congrArg (fun z : ℤ => (z : ℚ)) hj

/-- Exact finite character orthogonality, including all sixteen root signs. -/
theorem epsilon_orthogonality (i j : Index) :
    (∑ b : Fin 4 → Bool, epsilon i b * epsilon j b) = if i = j then 16 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (epsilonInt_orthogonality i j)
  simpa [Int.cast_sum, Int.cast_mul, epsilonInt_cast] using h

end SourceHOneCharacterIndices318
