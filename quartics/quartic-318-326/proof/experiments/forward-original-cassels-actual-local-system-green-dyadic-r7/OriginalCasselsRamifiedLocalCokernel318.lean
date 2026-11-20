module
public import OriginalCasselsRamifiedClasses318
public import OriginalCasselsRamifiedRootCriterion318
import all OriginalCasselsOddLocalFinite318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
import all OriginalCasselsDyadicXClass318
public section

noncomputable section

namespace OriginalCasselsRamifiedLocalCokernel318

open OriginalCasselsRamifiedClasses318 OriginalCasselsRamifiedRootCriterion318
open OriginalCasselsOddLocalFinite318 OriginalSelectedCasselsParity318
open OriginalCasselsLiteralRangeFinite318 OriginalCasselsDyadicXClass318
open OriginalCasselsTargetClassChord318 OriginalCasselsLiteralIsogenyPoint318
open OriginalCasselsLiteralIsogenyAddition318 OriginalCasselsOddUnitSquare318

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- The exact selected ramified local cardinality, on the same actual
literal L produced by finite residue representatives and group addition. -/
theorem actual_ramified_cokernel_card (hp : 5≤p) (hp2 : p≠2)
    (n : ℚ_[p]) (hn : n≠0) (hvn : ((4:ℚ_[p])*n).valuation=1) :
    (localOddIsogeny hp2 n hn).cokernelCard = if p%3=1 then 2 else 1 := by
  let H := xClassHom (actual_target_class_product n hn)
  let img (P : TargetPoint n) : H.range := ⟨H P,⟨P,rfl⟩⟩
  change Nat.card (TargetPoint n ⧸ (literalHom (literal_addition n hn)).range)=_
  rw [Nat.card_congr (literalQuotientEquiv n hn).toEquiv]
  by_cases h3 : p%3=1
  · rw [if_pos h3]
    obtain ⟨r,hr⟩ := (root_iff_residue_one p hp).mpr h3
    obtain ⟨P₀,hne,hclasses⟩ := ramified_actual_two_classes hp hp2 n hn hvn r hr
    let f : Bool → H.range := fun b => if b then img P₀ else img 0
    have hf : f true≠f false := by
      intro h
      apply hne
      exact congrArg Subtype.val h
    have hI : Function.Injective f := by
      intro a b h
      cases a <;> cases b
      · rfl
      · exact (hf h.symm).elim
      · exact (hf h).elim
      · rfl
    have hS : Function.Surjective f := by
      rintro ⟨z,P,rfl⟩
      rcases hclasses P with h|h
      · exact ⟨false,Subtype.ext h.symm⟩
      · exact ⟨true,Subtype.ext h.symm⟩
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hI,hS⟩).symm,Nat.card_eq_fintype_card] <;> decide
  · rw [if_neg h3]
    have hN : ¬∃ r : ZMod p, r^2-r+1=0 := fun h => h3 ((root_iff_residue_one p hp).mp h)
    let f : Unit → H.range := fun _ => img 0
    have hF : Function.Bijective f := by
      constructor
      · intro a b _
        exact Subsingleton.elim a b
      · rintro ⟨z,P,rfl⟩
        exact ⟨(),Subtype.ext (ramified_target_class_one_of_no_root hp2 n hn hvn hN P).symm⟩
    rw [Nat.card_congr (Equiv.ofBijective f hF).symm,Nat.card_eq_fintype_card] <;> decide

end OriginalCasselsRamifiedLocalCokernel318

#print axioms OriginalCasselsRamifiedLocalCokernel318.actual_ramified_cokernel_card
