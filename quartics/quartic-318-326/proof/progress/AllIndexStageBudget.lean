module
public import Height13RealLog
public section
namespace AllIndexStageBudget

/-- Precision loss after normalization and unary division, allowing δ<0. -/
theorem protected_unary_division (delta W U M R : ℝ)
    (hU : U ≤ W) (hR : 2 ≤ R)
    (hM : max 0 (delta+W)+R ≤ M) :
    1 ≤ M-(delta+U)-1 := by
  have hn : delta+W ≤ max 0 (delta+W) := le_max_right _ _
  linarith

/-- The all-index coarse bound pays the entire finite operator budget
    outside the bounded squarefree window. v is the numerator valuation. -/
theorem outside_window (delta W U M R T C D v : ℝ)
    (hU : U ≤ W) (hT : max 0 (delta+W)+R ≤ T-C)
    (hD : T < D) (hM : max 0 (delta+W)+R ≤ M)
    (hv : min M (D-C) ≤ v) :
    R ≤ v-(delta+U) := by
  have hn : delta+W ≤ max 0 (delta+W) := le_max_right _ _
  have hb : max 0 (delta+W)+R ≤ min M (D-C) := by
    apply le_min hM
    linarith
  linarith

/-- The bounded odd minimum plus the J shell factors yields the desired
    lower bound; both original and recurrence errors are included in M. -/
theorem inside_window (delta W U J r M R v : ℝ)
    (hU : U ≤ W) (hJ : 0 ≤ J)
    (hM : max 0 (delta+W)+R ≤ M)
    (hv : min M (min M (delta+(U-J+r))+J) ≤ v) :
    min R r ≤ v-(delta+U) := by
  have hn : delta+W ≤ max 0 (delta+W) := le_max_right _ _
  have hr : min R r ≤ R := min_le_left _ _
  have hrr : min R r ≤ r := min_le_right _ _
  have hb : delta+U+min R r ≤ min M (min M (delta+(U-J+r))+J) := by
    apply le_min
    · linarith
    · have hi : delta+U+min R r-J ≤ min M (delta+(U-J+r)) := by
        apply le_min <;> linarith
      linarith
  linarith

/-- This is the finite-budget, every-Fourier-index conclusion of F.6→O.9.
    Only the inside-window branch needs the attained odd minimum. -/
theorem every_index (delta W U J r M R T C D v : ℝ)
    (hU : U ≤ W) (hJ : 0 ≤ J) (hD : D = U-J+r)
    (hT : max 0 (delta+W)+R ≤ T-C)
    (hM : max 0 (delta+W)+R ≤ M)
    (hsmall : D ≤ T → min M (min M (delta+D)+J) ≤ v)
    (hlarge : T < D → min M (D-C) ≤ v) :
    min R r ≤ v-(delta+U) := by
  by_cases hd : D ≤ T
  · apply inside_window delta W U J r M R v hU hJ hM
    simpa [hD] using hsmall hd
  · have hb := outside_window delta W U M R T C D v hU hT (lt_of_not_ge hd) hM (hlarge (lt_of_not_ge hd))
    exact (min_le_left R r).trans hb

/-- The same stage pays the omitted U\{p} normalization as well. No new
    depth or coefficient source is introduced by whole-prime omission. -/
theorem omission_precision (delta W U M R : ℝ)
    (hU : U ≤ W) (hR : 2 ≤ R)
    (hM : max 0 (delta+W)+R ≤ M) :
    1 ≤ M-(delta+U)-1 ∧ 1 ≤ M-(delta+(U-1))-1 := by
  have h := protected_unary_division delta W U M R hU hR hM
  constructor
  · exact h
  · linarith

#print axioms protected_unary_division
#print axioms outside_window
#print axioms inside_window
#print axioms every_index
#print axioms omission_precision
end AllIndexStageBudget
