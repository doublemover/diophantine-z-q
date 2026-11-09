module
public import ActualSourceHOneSmallPoles318
public import SourceCharacterFields318

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

theorem epsilon_square (i : Index) (b : Fin 4 → Bool) : epsilon i b ^ 2 = 1 := by
  revert i b
  decide

theorem epsilon_separates : ∀ i j : Index, i ≠ j →
    ∃ b : Fin 4 → Bool, epsilon i b = 1 ∧ epsilon j b = -1 := by decide

/-- Exact finite character orthogonality, including all sixteen root signs. -/
theorem epsilon_orthogonality (i j : Index) :
    (∑ b : Fin 4 → Bool, epsilon i b * epsilon j b) = if i = j then 16 else 0 := by
  revert i j
  decide

end SourceHOneCharacterIndices318
