module
public import SelectedTraceFromOrders318
public section
noncomputable section
namespace SelectedVariableDenominatorUnit318
open ValuativeOrbitBounds318 ConcretePadic318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Two different positive prime values already force the variable w to be
unit at the selected prime. This is not a new avoidance condition on w. -/
theorem variable_unit (hn : ∀ j, labels j≠0) (u w : ℤ) (hp : Values C u w)
    (j : Fin 3) (i : Fin 5) :
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    rationalPlace p (w:ℚ)=0 := by
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  let v := rationalPlace p
  let l : Fin 5 := if i=0 then 1 else 0
  have hli : l≠i := by
    dsimp [l]
    split_ifs with hi
    · subst i; decide
    · exact Ne.symm hi
  have hvals := SelectedProductDepth318.factor_values (row C u w j)
    (row_pos C u w hp j) (row_prime C u w hp j) (row_distinct C hn u w hp j) i
  have hi : v (row C u w j i:ℚ)=1 := by simpa only [ite_true] using hvals i
  have hl : v (row C u w j l:ℚ)=0 := by simpa only [if_neg hli] using hvals l
  have hd : v ((row C u w j i:ℚ)-(row C u w j l:ℚ))=0 := by
    rw [v.map_sub_eq_of_lt_right (by rw [hl,hi]; norm_num),hl]
  have hw0 : (0:WithTop ℤ)≤v (w:ℚ) := IntegralPolynomialPrecision318.int_bound v w
  by_contra hw
  have hwpos : 0<v (w:ℚ) := lt_of_le_of_ne hw0 (Ne.symm hw)
  have hc : (0:WithTop ℤ)≤v ((C.coefficient (j,i)-C.coefficient (j,l):ℤ):ℚ) :=
    IntegralPolynomialPrecision318.int_bound v _
  have hpositive : 0<v (((C.coefficient (j,i)-C.coefficient (j,l):ℤ):ℚ)*(w:ℚ)*(w:ℚ)) := by
    rw [v.map_mul,v.map_mul]
    exact add_pos_of_nonneg_of_pos (add_nonneg hc hw0) hwpos
  have he : (row C u w j i:ℚ)-(row C u w j l:ℚ)=
      ((C.coefficient (j,i)-C.coefficient (j,l):ℤ):ℚ)*(w:ℚ)*(w:ℚ) := by
    simp only [row,value,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_pow]
    ring
  rw [←he,hd] at hpositive
  exact (lt_irrefl _ hpositive)

end SelectedVariableDenominatorUnit318
