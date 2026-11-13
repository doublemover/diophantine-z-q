module
public import FiniteOrderSignCandidates318
public section
noncomputable section
namespace ActualRootSwapOrders318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedRayEmbeddings318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
lemma primary_swap (r : Roots C u w hv) (s : Fin 3 × Fin 5 → Bool) (i : Fin 3 × Fin 5) :
    primaryOrder C u w hv (oriented C u w hv r s) i=
      FiniteOrderSignChoices318.left (primaryOrder C u w hv r) (oppositeOrder C u w hv r) s i := by
  cases h : s i <;> simp only [primaryOrder,oppositeOrder,oriented,
    FiniteOrderSignChoices318.left,h,Bool.false_eq_true,if_false,if_true]
lemma opposite_swap (r : Roots C u w hv) (s : Fin 3 × Fin 5 → Bool) (i : Fin 3 × Fin 5) :
    oppositeOrder C u w hv (oriented C u w hv r s) i=
      FiniteOrderSignChoices318.right (primaryOrder C u w hv r) (oppositeOrder C u w hv r) s i := by
  cases h : s i <;> simp only [primaryOrder,oppositeOrder,oriented,
    FiniteOrderSignChoices318.right,h,Bool.false_eq_true,if_false,if_true,neg_neg]
lemma minus_swap (r : Roots C u w hv) (s : Fin 3 × Fin 5 → Bool) :
    minus C u w hv (oriented C u w hv r s)=
      FiniteOrderSignChoices318.leftLCM (primaryOrder C u w hv r) (oppositeOrder C u w hv r) s := by
  unfold minus FiniteOrderSignChoices318.leftLCM
  apply congrArg (fun f : Fin 3 × Fin 5 → ℕ => Finset.univ.lcm f)
  funext i
  exact primary_swap C u w hv r s i
lemma plus_swap (r : Roots C u w hv) (s : Fin 3 × Fin 5 → Bool) :
    plus C u w hv (oriented C u w hv r s)=
      FiniteOrderSignChoices318.rightLCM (primaryOrder C u w hv r) (oppositeOrder C u w hv r) s := by
  unfold plus FiniteOrderSignChoices318.rightLCM
  apply congrArg (fun f : Fin 3 × Fin 5 → ℕ => Finset.univ.lcm f)
  funext i
  exact opposite_swap C u w hv r s i
end ActualRootSwapOrders318
