module
public import ActualA4LinearNormCard318
public section
noncomputable section
namespace ActualA4ProjectiveUnion318

open scoped BigOperators
open ActualA4LinearNormCard318
variable {F J : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]

@[expose] def unionMask (a b : J → F) : Finset (TwoPlanes F) :=
  Finset.univ.biUnion (fun j => zeroSet (a j) (b j))

theorem core_le_union (a b : J → F) (j : J) :
    core ⊆ unionMask a b := by
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,core_subset _ _ hz⟩

/-- Every off-core point lies in exactly ONE projective mask. The
multiplicity correction is exactly (r−1) times the common core. -/
theorem exact_union (a b : J → F) (j : J)
    (h : ∀ k l, k ≠ l → a k*b l-a l*b k ≠ 0) :
    ((unionMask a b).card:ℤ) =
      (∑ k : J, ((zeroSet (a k) (b k)).card:ℤ)) -
        ((Fintype.card J:ℤ)-1)*((core : Finset (TwoPlanes F)).card:ℤ) := by
  let outside k := zeroSet (a k) (b k) \ (core : Finset (TwoPlanes F))
  have heq : unionMask a b \ (core : Finset (TwoPlanes F)) =
      Finset.univ.biUnion outside := by
    ext z
    constructor
    · intro hz
      obtain ⟨hU,hN⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨k,hk,hV⟩ := Finset.mem_biUnion.mp hU
      exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_sdiff.mpr ⟨hV,hN⟩⟩
    · intro hz
      obtain ⟨k,hk,hV⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hZ,hN⟩ := Finset.mem_sdiff.mp hV
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨k,hk,hZ⟩,hN⟩
  have hdisj : (↑(Finset.univ:Finset J) : Set J).PairwiseDisjoint outside := by
    intro k _ l _ hkl
    apply Finset.disjoint_left.mpr
    intro z hk hl
    obtain ⟨hkZ,hkN⟩ := Finset.mem_sdiff.mp hk
    have hlZ := (Finset.mem_sdiff.mp hl).1
    have hI := Finset.mem_inter.mpr ⟨hkZ,hlZ⟩
    rw [common_intersection (h k l hkl)] at hI
    exact hkN hI
  have hCount : ((unionMask a b).card:ℤ) =
      (∑ k : J, ((outside k).card:ℤ)) + ((core : Finset (TwoPlanes F)).card:ℤ) := by
    have H := Finset.card_sdiff_add_card_eq_card (core_le_union a b j)
    rw [heq,Finset.card_biUnion hdisj] at H
    exact_mod_cast H.symm
  have hOut (k : J) : ((outside k).card:ℤ) =
      ((zeroSet (a k) (b k)).card:ℤ)-((core : Finset (TwoPlanes F)).card:ℤ) := by
    have H := Finset.card_sdiff_add_card_eq_card (core_subset (a k) (b k))
    have H' : ((outside k).card:ℤ)+((core : Finset (TwoPlanes F)).card:ℤ)=
        ((zeroSet (a k) (b k)).card:ℤ) := by exact_mod_cast H
    omega
  simp_rw [hOut] at hCount
  rw [Finset.sum_sub_distrib] at hCount
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hCount
  rw [hCount]
  ring

@[expose] def norm0 (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℤ :=
    (Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F)

@[expose] def rankFour (F : Type*) [Fintype F] : ℤ :=
    (Fintype.card F:ℤ)^3+(Fintype.card F:ℤ)^2-(Fintype.card F:ℤ)

theorem two_axes_exact (a b : J → F) (i j : J) (hij : i ≠ j)
    (hi : a i ≠ 0 ∧ b i=0) (hj : a j=0 ∧ b j ≠ 0)
    (hproj : ∀ k l, k ≠ l → a k*b l-a l*b k ≠ 0)
    (hf : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    ((unionMask a b).card:ℤ) =
      2*norm0 F*(Fintype.card F:ℤ)^2+((Fintype.card J:ℤ)-2)*rankFour F-
          ((Fintype.card J:ℤ)-1)*(norm0 F)^2 := by
  let A := norm0 F*(Fintype.card F:ℤ)^2-rankFour F
  have hEach (k : J) : ((zeroSet (a k) (b k)).card:ℤ)=rankFour F+
      (if k=i then A else 0)+(if k=j then A else 0) := by
    by_cases hki : k=i
    · subst k
      rw [hi.2,first_card hf (a i) hi.1,if_pos rfl,if_neg hij]
      simp only [A,norm0,add_zero,zero_add,ite_true] <;> ring
    · by_cases hkj : k=j
      · subst k
        rw [hj.1,second_card hf (b j) hj.2,if_neg hki,if_pos rfl]
        simp only [A,norm0,add_zero,zero_add,ite_true] <;> ring
      · have hak : a k ≠ 0 := by
          intro hz
          have H := hproj k j hkj
          rw [hz,hj.1,zero_mul,zero_mul,sub_self] at H
          exact H rfl
        have hbk : b k ≠ 0 := by
          intro hz
          have H := hproj k i hki
          rw [hz,hi.2,mul_zero,mul_zero,sub_self] at H
          exact H rfl
        rw [rank_four_card hf h2 (a k) (b k) hak hbk,if_neg hki,if_neg hkj]
        simp [rankFour]
  rw [exact_union a b i hproj]
  simp_rw [hEach]
  rw [show (((core : Finset (TwoPlanes F)).card:ℤ))=(norm0 F)^2 from core_card hf]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp [A]
  <;> ring

end ActualA4ProjectiveUnion318
