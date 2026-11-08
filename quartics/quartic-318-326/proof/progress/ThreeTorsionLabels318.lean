module
public import PrimitiveDiamond318
public section
noncomputable section
namespace ThreeTorsionLabels318
open PrimitiveDiamond318
set_option maxHeartbeats 0
local instance : DecidablePred (PrimitiveTorsion318.Primitive 3) :=
  fun x=>inferInstanceAs (Decidable (Nat.gcd 3 (Nat.gcd x.1.val x.2.val)=1))
abbrev Index:=Fin 4×Bool
@[expose] def vector : Fin 4→ZMod 3×ZMod 3 := ![(1,0),(0,1),(1,1),(1,2)]
@[expose] def label (i:Index) : Points 3 :=
  ⟨if i.2 then -vector i.1 else vector i.1,by
    rcases i with ⟨i,b⟩
    fin_cases i <;> cases b <;> decide⟩
lemma label_bijective : Function.Bijective label := by
  change Function.Injective label ∧ Function.Surjective label
  decide
@[expose] def labels : Index≃Points 3:=Equiv.ofBijective label label_bijective
@[expose] def flip (i:Index) : Index:=(i.1,!i.2)

lemma unit_cases (g:(ZMod 3)ˣ) : g=1 ∨ g= -1 := by
  have hh:∀g:(ZMod 3)ˣ,g=1 ∨ g= -1:=by decide
  exact hh g
lemma neg_one_ne_one : (-1:(ZMod 3)ˣ)≠1 := by decide
lemma label_flip (i:Index) : label (flip i)=(-1:(ZMod 3)ˣ)•label i := by
  rcases i with ⟨i,b⟩
  fin_cases i <;> cases b <;> apply Subtype.ext <;> decide

end ThreeTorsionLabels318
