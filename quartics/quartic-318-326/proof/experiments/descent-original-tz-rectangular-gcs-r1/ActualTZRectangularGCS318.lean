module
public import ActualTZReflectionIteration318
import all Mathlib.Data.Fin.Tuple.Basic
public section
noncomputable section
namespace ActualTZRectangularGCS318
open scoped BigOperators
open ActualTZReflectionIteration318

@[expose] def pick {a : ℕ} {U : Type*} (u v : Fin a→U) (ω : Vertex a) : Fin a→U :=
  fun j => if ω j then u j else v j

/-- One shared parameter x is retained by all vertices. Both tuples of
each coordinate are summed independently, before any normalization. -/
def rect {a : ℕ} {U X : Type*} [Fintype U] [Fintype X]
    (F : Vertex a→X→(Fin a→U)→ℝ) : ℝ :=
  ∑ z : X×((Fin a→U)×(Fin a→U)), ∏ ω : Vertex a, F ω z.1 (pick z.2.1 z.2.2 ω)

private def splitArgs (a : ℕ) (j : Fin (a+1)) (U X : Type*) :
    (X×((Fin (a+1)→U)×(Fin (a+1)→U))) ≃ (X×((Fin a→U)×(Fin a→U)))×(U×U) where
  toFun z := ((z.1,(Fin.removeNth j z.2.1,Fin.removeNth j z.2.2)),(z.2.1 j,z.2.2 j))
  invFun z := (z.1.1,(Fin.insertNth j z.2.1 z.1.2.1,Fin.insertNth j z.2.2 z.1.2.2))
  left_inv z := by
    rcases z with ⟨x,u,v⟩
    simp only [Fin.insertNth_self_removeNth]
  right_inv z := by
    rcases z with ⟨⟨x,u,v⟩,s,t⟩
    simp

private theorem pick_insert {a : ℕ} {U : Type*} (j : Fin (a+1))
    (s t : U) (u v : Fin a→U) (b : Bool) (ω : Vertex a) :
    pick (Fin.insertNth j s u) (Fin.insertNth j t v) (Fin.insertNth j b ω) =
      Fin.insertNth j (if b then s else t) (pick u v ω) := by
  funext i
  cases i using Fin.succAboveCases j with
  | x => simp only [pick,Fin.insertNth_apply_same]
  | p i => simp only [pick,Fin.insertNth_apply_succAbove]

private def slice {a : ℕ} {U X : Type*} (j : Fin (a+1)) (b : Bool)
    (F : Vertex (a+1)→X→(Fin (a+1)→U)→ℝ)
    (z : X×((Fin a→U)×(Fin a→U))) (t : U) : ℝ :=
  ∏ ω : Vertex a, F (Fin.insertNth j b ω) z.1 (Fin.insertNth j t (pick z.2.1 z.2.2 ω))

private theorem vertex_product {a : ℕ} {U X : Type*} (j : Fin (a+1))
    (F : Vertex (a+1)→X→(Fin (a+1)→U)→ℝ)
    (z : X×((Fin a→U)×(Fin a→U))) (s t : U) :
    (∏ ω : Vertex (a+1), F ω z.1
      (pick (Fin.insertNth j s z.2.1) (Fin.insertNth j t z.2.2) ω)) =
      slice j true F z s*slice j false F z t := by
  let V (ω : Vertex (a+1)) := F ω z.1
    (pick (Fin.insertNth j s z.2.1) (Fin.insertNth j t z.2.2) ω)
  let e := Fin.insertNthEquiv (fun _ : Fin (a+1) => Bool) j
  calc
    _ = ∏ p : Bool×Vertex a,V (e p) := (e.prod_comp V).symm
    _ = ∏ b : Bool, ∏ ω : Vertex a,V (Fin.insertNth j b ω) := by
      rw [Fintype.prod_prod_type] <;> rfl
    _ = _ := by
      rw [Fintype.prod_bool]
      simp only [V,pick_insert,if_pos (rfl : true=true),Bool.false_eq_true,if_false,slice]

private theorem rect_factor {a : ℕ} {U X : Type*} [Fintype U] [Fintype X]
    (j : Fin (a+1)) (F : Vertex (a+1)→X→(Fin (a+1)→U)→ℝ) :
    rect F = ∑ z : X×((Fin a→U)×(Fin a→U)),
      (∑ s : U,slice j true F z s)*(∑ t : U,slice j false F z t) := by
  let e := splitArgs a j U X
  let V (z : X×((Fin (a+1)→U)×(Fin (a+1)→U))) := ∏ ω : Vertex (a+1), F ω z.1 (pick z.2.1 z.2.2 ω)
  have hV (z : X×((Fin a→U)×(Fin a→U))) (s t : U) :
      V (e.symm (z,(s,t)))=slice j true F z s*slice j false F z t :=
    vertex_product j F z s t
  calc
    _ = ∑ p : (X×((Fin a→U)×(Fin a→U)))×(U×U), V (e.symm p) := (e.symm.sum_comp V).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      simp only [hV,Finset.mul_sum]

private theorem reflected_factor {a : ℕ} {U X : Type*} [Fintype U] [Fintype X]
    (j : Fin (a+1)) (b : Bool) (F : Vertex (a+1)→X→(Fin (a+1)→U)→ℝ) :
    rect (mirror j b F) = ∑ z : X×((Fin a→U)×(Fin a→U)), (∑ t : U,slice j b F z t)^2 := by
  have h (c : Bool) (z : X×((Fin a→U)×(Fin a→U))) (t : U) :
      slice j c (mirror j b F) z t=slice j b F z t := by
    simp only [slice,mirror,Fin.update_insertNth]
  rw [rect_factor j]
  simp only [h,pow_two]

theorem reflect_cs {a : ℕ} {U X : Type*} [Fintype U] [Fintype X]
    (j : Fin a) (F : Vertex a→X→(Fin a→U)→ℝ) :
    |rect F|^2≤ |rect (mirror j true F)| * |rect (mirror j false F)| := by
  have ha : a≠0 := by have := j.isLt; omega
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [rect_factor j F,reflected_factor j true F,reflected_factor j false F]
  rw [sq_abs,abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem rectangular_gcs {a : ℕ} {U X : Type*} [Fintype U] [Fintype X]
    (F : Vertex a→X→(Fin a→U)→ℝ) :
    |rect F|^(2^a:ℕ)≤∏ ω : Vertex a, |rect (fun _ => F ω)| :=
  full_bound rect reflect_cs F

end ActualTZRectangularGCS318
