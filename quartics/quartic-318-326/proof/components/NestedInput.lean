module
public import QuarticOptimization
public section
namespace NestedInput
open QuarticOptimization

theorem nested_squarefree_input (q : ℚ) (a : ℕ) (ha : Squarefree a) (c d : ℤ) :
    (∃ n : ℤ, ((a : ℚ)*q^2+c)^2+d = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ :=
      (shifted_squarefree_square_integral ((a : ℚ)*q^2+c) 1 squarefree_one d).mp
        (by simpa using h)
    exact (shifted_squarefree_square_integral q a ha c).mp ⟨n, hn.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨((a : ℤ)*z^2+c)^2+d, by push_cast; ring⟩

theorem input_102_357_square_integral (q : ℚ) :
    (∃ n : ℤ, (102*q^2+357)^2 = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  simpa using nested_squarefree_input q 102 nat_102_squarefree 357 0

end NestedInput
