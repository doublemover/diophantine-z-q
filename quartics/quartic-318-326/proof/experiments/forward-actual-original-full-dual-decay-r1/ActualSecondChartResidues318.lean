module
public import ActualSecondChartIdentity318
public section
noncomputable section
namespace ActualSecondChartResidues318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318 OriginalQuadraticResidueCount318
open ActualSecondChartIdentity318
set_option maxHeartbeats 7000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def actualZeros (κ t : F) : Finset (Vector F) :=
  Finset.univ.filter (fun y => P' κ t y=0 ∧ K κ t y=0)

/-- Actual quartic zero set maps to SHIFTED norm factors only for this
regular residue branch. The original t remains in P' throughout. -/
theorem regular_card (κ t : F) (ht : t≠0) (ha : κ*(t+2)≠0) :
    (actualZeros κ t).card≤8*Fintype.card F := by
  classical
  let Target := Σ a : ↥(normPairs (t+2)), ↥(roots (κ*(t+2)) (2*a.1.1*a.1.2))
  let f : ↥(actualZeros κ t) → Target := fun a =>
    ⟨⟨(a.1.1,a.1.2.1),by
      have he : P' κ t a.1=0 ∧ K κ t a.1=0 := by simpa only
        [actualZeros,Finset.mem_filter,Finset.mem_univ,true_and] using a.2
      exact (mem_normPairs (t+2) _).mpr (shifted_zero κ t ht a.1 he.1 he.2)⟩,
     ⟨a.1.2.2,by
      have he : P' κ t a.1=0 ∧ K κ t a.1=0 := by simpa only
        [actualZeros,Finset.mem_filter,Finset.mem_univ,true_and] using a.2
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
  have htarget : Nat.card Target≤2*(normPairs (t+2)).card := by
    change Nat.card (Σ a : ↥(normPairs (t+2)), ↥(roots (κ*(t+2)) (2*a.1.1*a.1.2)))≤_
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_coe]
    calc
      ∑ a : ↥(normPairs (t+2)), (roots (κ*(t+2)) (2*a.1.1*a.1.2)).card≤∑ _a : ↥(normPairs (t+2)),2 :=
        Finset.sum_le_sum (fun a _ => roots_card _ _ ha)
      _ = 2*(normPairs (t+2)).card := by simp [mul_comm]
  have hnorm := normPairs_card (t+2)
  have hmain : (actualZeros κ t).card≤2*(normPairs (t+2)).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc.trans htarget
  omega


/-- At primes where t+2=0, including the entire original t=-2 slice,
the actual quartic on each axis is kappa²w⁴+4q². Count q at fixed w,
not w at fixed q; no nonzero quartic leading coefficient is required. -/
theorem exceptional_card (κ t : F) (ht : t≠0) (ht2 : t+2=0) :
    (actualZeros κ t).card≤4*Fintype.card F := by
  classical
  have htwo : (2:F)≠0 := by
    intro h
    rw [h,add_zero] at ht2
    exact ht ht2
  have hfour : (4:F)≠0 := by
    have he : (4:F)=2*2 := by norm_num
    rw [he]
    exact mul_ne_zero htwo htwo
  let A := Σ w : F, ↥(roots (4:F) (-κ^2*w^4))
  let leftAxis : A → Vector F := fun a => (0,a.2.1,a.1)
  let rightAxis : A → Vector F := fun a => (a.2.1,0,a.1)
  have hA : Fintype.card A≤2*Fintype.card F := by
    simp only [A,Fintype.card_sigma,Fintype.card_coe]
    calc
      _ ≤ ∑ _w : F, 2 := Finset.sum_le_sum (fun w _ => roots_card _ _ hfour)
      _ = _ := by simp [mul_comm]
  have hs : actualZeros κ t⊆Finset.univ.image leftAxis ∪ Finset.univ.image rightAxis := by
    intro y hy
    have he : P' κ t y=0 ∧ K κ t y=0 := by
      simpa only [actualZeros,Finset.mem_filter,Finset.mem_univ,true_and] using hy
    have hzero : y.1*y.2.1=0 := by
      have hh : (2:F)*(y.1*y.2.1)=0 := by
        dsimp [P'] at he
        rw [ht2,mul_zero,zero_mul,zero_sub,neg_eq_zero] at he
        simpa only [mul_assoc] using he.1
      exact (mul_eq_zero.mp hh).resolve_left htwo
    rcases mul_eq_zero.mp hzero with hx|hz
    · have hK : κ^2*y.2.2^4+4*y.2.1^2=0 := by
        have hh := he.2
        rw [show y=(0,y.2.1,y.2.2) by exact Prod.ext hx rfl,exceptional_x κ t _ _ ht2] at hh
        exact hh
      have hr : y.2.1∈roots (4:F) (-κ^2*y.2.2^4) := by
        apply (mem_roots _ _ _).mpr
        linear_combination hK
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨y.2.2,⟨y.2.1,hr⟩⟩,Finset.mem_univ _,by
        dsimp [leftAxis]
        exact Prod.ext hx.symm rfl⟩
    · have hK : κ^2*y.2.2^4+4*y.1^2=0 := by
        have hh := he.2
        rw [show y=(y.1,0,y.2.2) by exact Prod.ext rfl (Prod.ext hz rfl),exceptional_z κ t _ _ ht2] at hh
        exact hh
      have hr : y.1∈roots (4:F) (-κ^2*y.2.2^4) := by
        apply (mem_roots _ _ _).mpr
        linear_combination hK
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨y.2.2,⟨y.1,hr⟩⟩,Finset.mem_univ _,by
        dsimp [rightAxis]
        exact Prod.ext rfl (Prod.ext hz.symm rfl)⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hl := Finset.card_image_le (s := (Finset.univ:Finset A)) (f := leftAxis)
  have hr := Finset.card_image_le (s := (Finset.univ:Finset A)) (f := rightAxis)
  simp only [Finset.card_univ] at hl hr
  omega

/-- Uniform8|F| for the ACTUAL original second Gaussian pair, with no
prime dividing t+2 discarded and no relabeling of the original lattice. -/
theorem actual_card (κ t : F) (hκ : κ≠0) (ht : t≠0) :
    (actualZeros κ t).card≤8*Fintype.card F := by
  by_cases ht2 : t+2=0
  · exact (exceptional_card κ t ht ht2).trans (by omega)
  · exact regular_card κ t ht (mul_ne_zero hκ ht2)

end ActualSecondChartResidues318
