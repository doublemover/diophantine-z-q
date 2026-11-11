module
public import ActualTwoDescentLocalCoefficientBound318
public section
noncomputable section
namespace ActualTwoDescentAuxiliaryTypes318
open ActualTwoDescentSymbolTable318
set_option maxHeartbeats 16000000

lemma actual_type_one (p : ℕ) (h : (p : ZMod 12)=1) :
    ((p/2 : ℕ) : ZMod 2)=0 ∧ symbolBit 3 p=0 := by
  have hm : p % 12=1 := (ZMod.natCast_eq_natCast_iff' p 1 12).mp h
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hj : jacobiSym 3 p=1 := by
    rw [jacobiSym.mod_right' 3 ho]
    change jacobiSym 3 (p % 12)=1
    rw [hm]
    norm_num
  constructor
  · apply (ZMod.natCast_eq_natCast_iff' (p/2) 0 2).mpr
    omega
  · simp [symbolBit,hj]

lemma actual_type_seven (p : ℕ) (h : (p : ZMod 12)=7) :
    ((p/2 : ℕ) : ZMod 2)=1 ∧ symbolBit 3 p=1 := by
  have hm : p % 12=7 := (ZMod.natCast_eq_natCast_iff' p 7 12).mp h
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hj : jacobiSym 3 p= -1 := by
    rw [jacobiSym.mod_right' 3 ho]
    change jacobiSym 3 (p % 12)= -1
    rw [hm]
    norm_num
  constructor
  · apply (ZMod.natCast_eq_natCast_iff' (p/2) 1 2).mpr
    omega
  · simp [symbolBit,hj]

lemma eq_add_of_add_eq (a b c : ZMod 2) (h : a+b=c) : a=b+c := by
  calc
    a=(a+b)+b := by rw [add_assoc,ActualTwoDescentIncidence318.actual_two_add,add_zero]
    _=c+b := by rw [h]
    _=b+c := add_comm _ _

end ActualTwoDescentAuxiliaryTypes318
