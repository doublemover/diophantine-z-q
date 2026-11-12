module
public import SelectedReductionOrder318
public import Mathlib.GroupTheory.Index
public section
noncomputable section
namespace FourTorsionQuotient318
set_option maxHeartbeats 1000000
variable {G : Type*} [AddCommGroup G]

lemma four_sum (A B : G) (hA : A+A=0) (hB : B+B=0) : (A+B)+(A+B)=0 := by
  calc
    _ = (A+A)+(B+B) := by abel
    _ = 0 := by rw [hA,hB,zero_add]

@[expose] def subgroup (A B : G) (hA : A+A=0) (hB : B+B=0) : AddSubgroup G where
  carrier := {x | x=0 ∨ x=A ∨ x=B ∨ x=A+B}
  zero_mem' := Or.inl rfl
  neg_mem' := by
    have nA : -A=A := neg_eq_iff_add_eq_zero.mpr hA
    have nB : -B=B := neg_eq_iff_add_eq_zero.mpr hB
    intro x hx
    rcases hx with rfl|rfl|rfl|rfl <;> simp only [neg_zero,neg_add,nA,nB] <;> tauto
  add_mem' := by
    have hAB_A : (A+B)+A=B := by calc
      _ = (A+A)+B := by abel
      _ = B := by rw [hA,zero_add]
    have hAB_B : (A+B)+B=A := by rw [add_assoc,hB,add_zero]
    have hA_AB : A+(A+B)=B := by rw [←add_assoc,hA,zero_add]
    have hB_AB : B+(A+B)=A := by rw [add_comm B (A+B),hAB_B]
    intro x y hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      (try simp only [zero_add,add_zero,hA,hB,hAB_A,hAB_B,hA_AB,hB_AB,four_sum A B hA hB,
        show B+A=A+B from add_comm B A]) <;> tauto

@[expose] def element (A B : G) (i : Fin 4) : G := ![0,A,B,A+B] i

lemma element_mem (A B : G) (hA : A+A=0) (hB : B+B=0) (i : Fin 4) :
    element A B i∈subgroup A B hA hB := by
  change element A B i=0 ∨ element A B i=A ∨ element A B i=B ∨ element A B i=A+B
  fin_cases i <;> simp [element]

lemma element_injective (A B : G) (hA : A+A=0) (hB : B+B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : A≠B) : Function.Injective (element A B) := by
  have hab0 : A+B≠0 := by
    intro he
    exact hAB (add_left_cancel (he.trans hA.symm)).symm
  have haba : A+B≠A := by
    intro he
    exact hB0 (add_left_cancel (he.trans (add_zero A).symm))
  have habb : A+B≠B := by
    intro he
    exact hA0 (add_right_cancel (he.trans (zero_add B).symm))
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [element]

theorem subgroup_card (A B : G) (hA : A+A=0) (hB : B+B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : A≠B) : Nat.card (subgroup A B hA hB)=4 := by
  let f : Fin 4 → subgroup A B hA hB := fun i => ⟨element A B i,element_mem A B hA hB i⟩
  have hi : Function.Injective f := by
    intro i j he
    exact element_injective A B hA hB hA0 hB0 hAB (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    intro x
    rcases x.2 with hx|hx|hx|hx
    · exact ⟨0,Subtype.ext (by simpa only [f,element,Matrix.cons_val_zero] using hx.symm)⟩
    · exact ⟨1,Subtype.ext (by simpa [f,element] using hx.symm)⟩
    · exact ⟨2,Subtype.ext (by simpa [f,element] using hx.symm)⟩
    · exact ⟨3,Subtype.ext (by simpa [f,element] using hx.symm)⟩
  calc
    Nat.card (subgroup A B hA hB)=Nat.card (Fin 4) := Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩).symm
    _ = 4 := by simp

lemma twice_mem_zero (A B : G) (hA : A+A=0) (hB : B+B=0)
    (x : G) (hx : x∈subgroup A B hA hB) : (2:ℕ) • x=0 := by
  rw [two_nsmul]
  rcases hx with rfl|rfl|rfl|rfl
  · exact zero_add _
  · exact hA
  · exact hB
  · exact four_sum A B hA hB

/-- Four ACTUAL distinct2-torsion points suffice: the exact order of any
double divides the ambient cardinality/4. No structure theorem or claim
that these exhaust the2-torsion is needed. -/
theorem double_order_dvd_quarter [Finite G] (A B : G) (hA : A+A=0) (hB : B+B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : A≠B) (Q : G) :
    addOrderOf (Q+Q)∣Nat.card G/4 := by
  let H := subgroup A B hA hB
  have hcard : Nat.card H=4 := subgroup_card A B hA hB hA0 hB0 hAB
  have hindex : H.index=Nat.card G/4 := by
    have he := H.card_mul_index
    rw [hcard] at he
    omega
  let q := QuotientAddGroup.mk' H
  have hz : H.index • q Q=0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard (q Q))
  have hm : H.index • Q∈H := by
    apply (QuotientAddGroup.eq_zero_iff (N := H) _).mp
    simpa only [map_nsmul] using hz
  have hh := twice_mem_zero A B hA hB _ hm
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
  rw [←hindex,nsmul_add]
  simpa only [two_nsmul] using hh

end FourTorsionQuotient318
