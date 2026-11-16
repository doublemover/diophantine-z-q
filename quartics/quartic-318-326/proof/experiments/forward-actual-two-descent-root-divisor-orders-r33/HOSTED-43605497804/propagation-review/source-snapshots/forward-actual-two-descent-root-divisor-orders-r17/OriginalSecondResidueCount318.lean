module
public import OriginalQuadraticResidueCount318
public section
noncomputable section
namespace OriginalSecondResidueCount318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318 OriginalQuadraticResidueCount318
set_option maxHeartbeats 4500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Regular second-pair count via the ACTUAL w-root fiber over each
original D-zero (x,z) pair. No independence of those fibers is assumed. -/
theorem second_regular_card (κ t : F) (ha : κ*(t+2)≠0) :
    (secondZeros κ t).card≤8*Fintype.card F := by
  classical
  let Target := Σ a : ↥(normPairs t), ↥(roots (κ*(t+2)) (2*a.1.1*a.1.2))
  let f : ↥(secondZeros κ t) → Target := fun a =>
    ⟨⟨(a.1.1,a.1.2.1),by
      have he : P' κ t a.1=0 ∧ D t a.1=0 := by simpa only
        [secondZeros,Finset.mem_filter,Finset.mem_univ,true_and] using a.2
      exact (mem_normPairs t _).mpr he.2⟩,
     ⟨a.1.2.2,by
      have he : P' κ t a.1=0 ∧ D t a.1=0 := by simpa only
        [secondZeros,Finset.mem_filter,Finset.mem_univ,true_and] using a.2
      apply (mem_roots _ _ _).mpr
      dsimp [P'] at he
      linear_combination he.1⟩⟩
  have hi : Function.Injective f := by
    intro a b he
    have hab := congrArg (fun c : Target => c.1.1) he
    have hw := congrArg (fun c : Target => c.2.1) he
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.fst hab) (Prod.ext (congrArg Prod.snd hab) hw)
  have hc := Nat.card_le_card_of_injective f hi
  have htarget : Nat.card Target≤2*(normPairs t).card := by
    change Nat.card (Σ a : ↥(normPairs t), ↥(roots (κ*(t+2)) (2*a.1.1*a.1.2)))≤_
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_coe]
    calc
      ∑ a : ↥(normPairs t), (roots (κ*(t+2)) (2*a.1.1*a.1.2)).card≤∑ _a : ↥(normPairs t),2 :=
        Finset.sum_le_sum (fun a _ => roots_card _ _ ha)
      _ = 2*(normPairs t).card := by simp [mul_comm]
  have hnorm := normPairs_card t
  have hmain : (secondZeros κ t).card≤2*(normPairs t).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc.trans htarget
  omega

/-- At t=-2 the w-quadratic coefficient vanishes. The two remaining
coordinate axes are counted separately, retaining the free w coordinate;
this branch is not discarded or treated by a false degree-two fiber bound. -/
theorem second_exceptional_card (κ t : F) (ht : t≠0) (ht2 : t+2=0) :
    (secondZeros κ t).card≤4*Fintype.card F := by
  let N := roots (1:F) (-t^2)
  have hN : N.card≤2 := roots_card 1 (-t^2) one_ne_zero
  have htwo : (2:F)≠0 := by
    intro h
    rw [h,add_zero] at ht2
    exact ht ht2
  have htSq : t^2≠0 := pow_ne_zero 2 ht
  have hs : secondZeros κ t⊆(({0}:Finset F)×ˢ(N×ˢ(Finset.univ:Finset F)))∪
      (N×ˢ(({0}:Finset F)×ˢ(Finset.univ:Finset F))) := by
    intro a ha
    have he : P' κ t a=0 ∧ D t a=0 := by simpa only
      [secondZeros,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    have hzero : a.1*a.2.1=0 := by
      have hh : (2:F)*(a.1*a.2.1)=0 := by
        dsimp [P'] at he
        rw [ht2,mul_zero,zero_mul,zero_sub,neg_eq_zero] at he
        simpa only [mul_assoc] using he.1
      exact (mul_eq_zero.mp hh).resolve_left htwo
    have hD : (t^2+a.1^2)*(t^2+a.2.1^2)=0 := he.2
    rcases mul_eq_zero.mp hzero with hx|hz
    · have hroot : a.2.1∈N := by
        rw [hx,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hD
        have hh := (mul_eq_zero.mp hD).resolve_left htSq
        apply (mem_roots 1 (-t^2) a.2.1).mpr
        linear_combination hh
      apply Finset.mem_union_left
      exact Finset.mem_product.mpr ⟨by simp [hx],Finset.mem_product.mpr ⟨hroot,Finset.mem_univ _⟩⟩
    · have hroot : a.1∈N := by
        rw [hz,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hD
        have hh := (mul_eq_zero.mp hD).resolve_right htSq
        apply (mem_roots 1 (-t^2) a.1).mpr
        linear_combination hh
      apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨hroot,Finset.mem_product.mpr ⟨by simp [hz],Finset.mem_univ _⟩⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product,Finset.card_univ,Finset.card_singleton,one_mul] at hc
  have hh := Nat.mul_le_mul_right (Fintype.card F) hN
  omega

/-- Uniform second original pair count, including its exceptional chart. -/
theorem secondZeros_card (κ t : F) (hκ : κ≠0) (ht : t≠0) :
    (secondZeros κ t).card≤8*Fintype.card F := by
  by_cases ht2 : t+2=0
  · exact (second_exceptional_card κ t ht ht2).trans (by omega)
  · exact second_regular_card κ t (mul_ne_zero hκ ht2)

end OriginalSecondResidueCount318
