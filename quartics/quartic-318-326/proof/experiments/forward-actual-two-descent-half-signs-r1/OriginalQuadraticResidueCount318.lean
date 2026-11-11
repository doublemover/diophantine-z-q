module
public import OriginalReducedDegreeBounds318
public section
noncomputable section
namespace OriginalQuadraticResidueCount318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318
set_option maxHeartbeats 4000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def roots (a b : F) : Finset F := Finset.univ.filter (fun x => a*x^2=b)
lemma mem_roots (a b x : F) : x∈roots a b ↔ a*x^2=b := by simp [roots]

/-- At most two solutions, with repeated/zero roots and characteristic2
included. No splitting assumption or chosen square root is supplied. -/
theorem roots_card (a b : F) (ha : a≠0) : (roots a b).card≤2 := by
  classical
  by_cases hex : ∃ z : F, a*z^2=b
  · obtain ⟨z,hz⟩ := hex
    have hs : roots a b⊆{z,-z} := by
      intro x hx
      have he : x^2=z^2 := mul_left_cancel₀ ha ((mem_roots a b x).mp hx |>.trans hz.symm)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h|h <;> simp [h]
    exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans (by simp))
  · have he : roots a b=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      exact hex ⟨x,(mem_roots a b x).mp hx⟩
    simp [he]

@[expose] def normPairs (t : F) : Finset (F×F) :=
  Finset.univ.filter (fun a => (t^2+a.1^2)*(t^2+a.2^2)=0)
lemma mem_normPairs (t : F) (a : F×F) : a∈normPairs t ↔ (t^2+a.1^2)*(t^2+a.2^2)=0 := by
  simp [normPairs]

/-- The original D=(t²+x²)(t²+z²) zero locus has at most4|F| points,
including overlap at the intersection of its two original factors. -/
theorem normPairs_card (t : F) : (normPairs t).card≤4*Fintype.card F := by
  let N := roots (1:F) (-t^2)
  have hN : N.card≤2 := roots_card 1 (-t^2) one_ne_zero
  have hs : normPairs t⊆(N×ˢ(Finset.univ:Finset F))∪((Finset.univ:Finset F)×ˢN) := by
    intro a ha
    rcases mul_eq_zero.mp ((mem_normPairs t a).mp ha) with h|h
    · apply Finset.mem_union_left
      apply Finset.mem_product.mpr
      refine ⟨(mem_roots 1 (-t^2) a.1).mpr ?_,Finset.mem_univ _⟩
      linear_combination h
    · apply Finset.mem_union_right
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _,(mem_roots 1 (-t^2) a.2).mpr ?_⟩
      linear_combination h
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product,Finset.card_univ] at hc
  have h1 := Nat.mul_le_mul_right (Fintype.card F) hN
  have h2 := Nat.mul_le_mul_left (Fintype.card F) hN
  omega

@[expose] def firstZeros (κ t : F) : Finset (Vector F) :=
  Finset.univ.filter (fun a => P κ t a=0 ∧ D t a=0)
@[expose] def secondZeros (κ t : F) : Finset (Vector F) :=
  Finset.univ.filter (fun a => P' κ t a=0 ∧ D t a=0)

/-- First original coprime-pair residue count, before changing any basis. -/
theorem firstZeros_card (κ t : F) (hκ : κ≠0) :
    (firstZeros κ t).card≤8*Fintype.card F := by
  let W := roots κ (-2*t)
  let N := roots (1:F) (-t^2)
  have hW : W.card≤2 := roots_card κ (-2*t) hκ
  have hN : N.card≤2 := roots_card 1 (-t^2) one_ne_zero
  have hs : firstZeros κ t⊆(N×ˢ((Finset.univ:Finset F)×ˢW))∪
      ((Finset.univ:Finset F)×ˢ(N×ˢW)) := by
    intro a ha
    have he : P κ t a=0 ∧ D t a=0 := by simpa only [firstZeros,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    have hw : a.2.2∈W := by
      apply (mem_roots κ (-2*t) a.2.2).mpr
      dsimp [P] at he
      linear_combination he.1
    have hd : (t^2+a.1^2)*(t^2+a.2.1^2)=0 := he.2
    rcases mul_eq_zero.mp hd with h|h
    · apply Finset.mem_union_left
      refine Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr ⟨Finset.mem_univ _,hw⟩⟩
      apply (mem_roots 1 (-t^2) a.1).mpr
      linear_combination h
    · apply Finset.mem_union_right
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨?_,hw⟩⟩
      apply (mem_roots 1 (-t^2) a.2.1).mpr
      linear_combination h
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product,Finset.card_univ] at hc
  have h1 := Nat.mul_le_mul hN (Nat.mul_le_mul_left (Fintype.card F) hW)
  have h2 := Nat.mul_le_mul_left (Fintype.card F) (Nat.mul_le_mul hN hW)
  omega

end OriginalQuadraticResidueCount318
