module
public import ActualQuadricTaylor318
public section
noncomputable section
namespace FiniteFiveAffineFiber318
open scoped BigOperators
set_option maxHeartbeats 18000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def Free (i : Fin 5) := ↥((Finset.univ : Finset (Fin 5)).erase i)
@[expose] def extend (i : Fin 5) (v : Free i → F) (u : F) : Fin 5 → F :=
  fun j => if h : j=i then u else v ⟨j,Finset.mem_erase.mpr ⟨h,Finset.mem_univ j⟩⟩
@[simp] lemma extend_pivot (i : Fin 5) (v : Free i → F) (u : F) : extend i v u i=u := by
  simp only [extend,dif_pos rfl]
@[simp] lemma extend_free (i : Fin 5) (v : Free i → F) (u : F) (j : Free i) :
    extend i v u j.1=v j := by
  simp only [extend,dif_neg (Finset.mem_erase.mp j.2).1]

lemma sum_split (i : Fin 5) (g x : Fin 5 → F) :
    (∑j,g j*x j)=(∑j : Free i,g j.1*x j.1)+g i*x i := by
  rw [Finset.sum_coe_sort]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm

@[expose] def Fiber (g : Fin 5 → F) (t : F) := {x : Fin 5 → F // ∑j,g j*x j=t}

/-- The unique original pivot coordinate is solved explicitly. The
other FOUR coordinates are genuinely free, not an assumed rank count. -/
@[expose] def fiberEquiv (g : Fin 5 → F) (t : F) (i : Fin 5) (hi : g i≠0) :
    Fiber g t ≃ (Free i → F) where
  toFun x j := x.1 j.1
  invFun v := ⟨extend i v ((t-∑j : Free i,g j.1*v j)/g i),by
    rw [sum_split]
    simp only [extend_free,extend_pivot]
    field_simp [hi]
    <;> ring⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hj : j=i
    · subst j
      rw [extend_pivot]
      apply (div_eq_iff hi).mpr
      have hh := x.2
      rw [sum_split i] at hh
      linear_combination -hh
    · simp only [extend,dif_neg hj]
  right_inv v := by
    funext j
    exact extend_free i v _ j

lemma free_card (i : Fin 5) : Fintype.card (Free i)=4 := by
  rw [Free,Fintype.card_coe,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ]
  rfl

/-- Exact cardinality of every affine linear fiber with an ACTUAL
nonzero coefficient in five variables. The constant t is unrestricted. -/
theorem actual_fiber_card (g : Fin 5 → F) (t : F) (hg : ∃i,g i≠0) :
    Nat.card (Fiber g t)=(Fintype.card F)^4 := by
  obtain ⟨i,hi⟩ := hg
  rw [Nat.card_congr (fiberEquiv g t i hi)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,Finset.prod_const,Finset.card_univ,free_card]

end FiniteFiveAffineFiber318
