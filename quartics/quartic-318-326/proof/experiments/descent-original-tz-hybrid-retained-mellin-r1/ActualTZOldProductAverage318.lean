module
public import Mathlib
public section
noncomputable section
namespace ActualTZOldProductAverage318
open scoped BigOperators

@[expose] def prob {A : Type*} [Fintype A] (F : A→ℝ) : ℝ :=
  (∑ a : A,F a)/(Fintype.card A:ℝ)

theorem nested {A B : Type*} [Fintype A] [Fintype B] (F : A→B→ℝ) :
    prob (fun a=>prob (F a))=prob (fun z : A×B=>F z.1 z.2) := by
  simp only [prob,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div,div_div]
  rw [mul_comm (Fintype.card B:ℝ)]

theorem permute {A B : Type*} [Fintype A] [Fintype B] (e : A≃B) (F : B→ℝ) :
    prob (F ∘ e)=prob F := by
  unfold prob
  rw [Fintype.card_congr e]
  exact congrArg (fun S : ℝ=>S/(Fintype.card B:ℝ)) (e.sum_comp F)

/-- No Jacobian or repeated x: the old sample rearranges from
(h,(x,k)), c to (h,(k,c)), x, with exactly one shared x. -/
def shared (H X K C : Type*) : (H×(X×K))×C≃(H×(K×C))×X where
  toFun z := ((z.1.1,z.1.2.2,z.2),z.1.2.1)
  invFun z := ((z.1.1,z.2,z.1.2.1),z.1.2.2)
  left_inv := by rintro ⟨⟨h,x,k⟩,c⟩; rfl
  right_inv := by rintro ⟨⟨h,k,c⟩,x⟩; rfl

theorem shared_average {H X K C : Type*} [Fintype H] [Fintype X] [Fintype K] [Fintype C]
    (F : H→X→K→C→ℝ) :
    prob (fun z : H×(X×K)=>prob (fun c : C=>F z.1 z.2.1 z.2.2 c))=
      prob (fun z : H×(K×C)=>prob (fun x : X=>F z.1 x z.2.1 z.2.2)) := by
  rw [nested,nested]
  exact permute (shared H X K C) _

end ActualTZOldProductAverage318
