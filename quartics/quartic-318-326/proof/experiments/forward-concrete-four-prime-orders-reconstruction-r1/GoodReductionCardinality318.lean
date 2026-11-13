module
public import IntegralFormalSeparation318
public import Mathlib.SetTheory.Cardinal.Finite
public section
noncomputable section
namespace GoodReductionCardinality318
open GoodReductionResidue318 GoodReductionLifting318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- Distinct actual residue points cannot represent the same formal coset.
This uses the actual difference formula, including the same-x tangent case. -/
theorem same_coset_residue (D : ℤ_[p]) (hD : ‖D‖=1) (P Q : IntegralCurve p D)
    (he : QuotientAddGroup.mk' (subgroup p D) (point p D hD P)=
      QuotientAddGroup.mk' (subgroup p D) (point p D hD Q)) :
    reduce p D P=reduce p D Q := by
  by_contra hr
  have hsep : ‖(P.1.1:ℚ_[p])-(Q.1.1:ℚ_[p])‖=1 ∨
      ‖(Q.1.2:ℚ_[p])-(P.1.2:ℚ_[p])‖=1 := by
    by_cases hx : PadicInt.toZMod P.1.1=PadicInt.toZMod Q.1.1
    · right
      have hy : PadicInt.toZMod Q.1.2≠PadicInt.toZMod P.1.2 := by
        intro hy
        exact hr (Subtype.ext (Prod.ext hx hy.symm))
      have hu := (residue_unit p (Q.1.2-P.1.2)).mp
        (by simpa only [map_sub,sub_ne_zero] using hy)
      simpa only [PadicInt.norm_def,PadicInt.coe_sub] using hu
    · left
      have hu := (residue_unit p (P.1.1-Q.1.1)).mp
        (by simpa only [map_sub,sub_ne_zero] using hx)
      simpa only [PadicInt.norm_def,PadicInt.coe_sub] using hu
  have hn := IntegralFormalSeparation318.separated_difference
    (NormedField.toAbsoluteValue ℚ_[p]) (ActualSplitOrbitEntry318.nonarchimedean p)
    (D:ℚ_[p]) (P.1.1:ℚ_[p]) (P.1.2:ℚ_[p]) (Q.1.1:ℚ_[p]) (Q.1.2:ℚ_[p])
    D.2 (nonsingular p D hD P) (nonsingular p D hD Q)
    P.1.1.2 P.1.2.2 Q.1.1.2 Q.1.2.2 hsep
  apply hn
  apply (QuotientAddGroup.eq_zero_iff (N := subgroup p D) _).mp
  change (QuotientAddGroup.mk' (subgroup p D)) (point p D hD P-point p D hD Q)=0
  simpa only [map_sub,sub_eq_zero] using he

lemma point_nonformal (D : ℤ_[p]) (hD : ‖D‖=1) (P : IntegralCurve p D) :
    point p D hD P∉subgroup p D := by
  intro he
  rcases he with hz|hx
  · exact Point.some_ne_zero _ hz
  · change 1< ‖(P.1.1:ℚ_[p])‖ at hx
    exact not_lt_of_ge P.1.1.2 hx

@[expose] def lift (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) (z : ResidueCurve p D) :
    IntegralCurve p D := (lift_residue p hp D hD z).choose
lemma reduce_lift (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) (z : ResidueCurve p D) :
    reduce p D (lift p hp D hD z)=z := (lift_residue p hp D hD z).choose_spec

@[expose] def code (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) :
    Option (ResidueCurve p D) → (E (D:ℚ_[p])).Point ⧸ subgroup p D
  | none => 0
  | some z => QuotientAddGroup.mk' (subgroup p D) (point p D hD (lift p hp D hD z))

lemma code_some_ne_zero (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) (z : ResidueCurve p D) :
    code p hp D hD (some z)≠0 := by
  intro he
  exact point_nonformal p D hD _ ((QuotientAddGroup.eq_zero_iff (N := subgroup p D) _).mp he)

theorem code_injective (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) :
    Function.Injective (code p hp D hD) := by
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some z => exact False.elim (code_some_ne_zero p hp D hD z he.symm)
  | some z =>
    cases b with
    | none => exact False.elim (code_some_ne_zero p hp D hD z he)
    | some t =>
      have hh := same_coset_residue p D hD (lift p hp D hD z) (lift p hp D hD t) he
      rw [reduce_lift,reduce_lift] at hh
      exact congrArg some hh

/-- Every original formal quotient class is either infinity or has integral
coordinates. Its exact residue lifts to a point in the same original class. -/
theorem code_surjective (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) :
    Function.Surjective (code p hp D hD) := by
  intro a
  obtain ⟨P,rfl⟩ := QuotientAddGroup.mk'_surjective (subgroup p D) a
  by_cases hf : P∈subgroup p D
  · refine ⟨none,?_⟩
    exact ((QuotientAddGroup.eq_zero_iff (N := subgroup p D) _).mpr hf).symm
  · cases P with
    | zero => exact False.elim (hf (AddSubgroup.zero_mem _))
    | some x y h =>
      have hx : ‖x‖≤1 := by
        by_contra! he
        exact hf (Or.inr (by simpa only [Point.xRep_some,Matrix.cons_val_zero] using he))
      have hy : ‖y‖≤1 := LocalDerivativeSeparation318.ordinate_integral
        (NormedField.toAbsoluteValue ℚ_[p]) (ActualSplitOrbitEntry318.nonarchimedean p)
        (D:ℚ_[p]) x y D.2 hx (FormalChartDouble.ordinate_equation _ _ _ h)
      let P : IntegralCurve p D := ⟨(⟨x,hx⟩,⟨y,hy⟩),by
        apply Subtype.ext
        exact FormalChartDouble.ordinate_equation _ _ _ h⟩
      refine ⟨some (reduce p D P),?_⟩
      exact same_residue_coset p hp D hD (lift p hp D hD (reduce p D P)) P
        (reduce_lift p hp D hD (reduce p D P))

/-- An actual bijection, not just a finite cover or a point-count bound. -/
@[expose] def equivalence (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) :
    Option (ResidueCurve p D) ≃ (E (D:ℚ_[p])).Point ⧸ subgroup p D :=
  Equiv.ofBijective (code p hp D hD) ⟨code_injective p hp D hD,code_surjective p hp D hD⟩

/-- Cardinality of the SAME actual formal quotient equals the literal
finite residue-curve count, including its identity. No group-law preservation
of reduction is needed or asserted by this cardinality theorem. -/
theorem cardinality (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1) :
    Nat.card ((E (D:ℚ_[p])).Point ⧸ subgroup p D)=1+Nat.card (ResidueCurve p D) := by
  classical
  rw [←Nat.card_congr (equivalence p hp D hD)]
  rw [Nat.card_eq_fintype_card,Fintype.card_option,Nat.card_eq_fintype_card]
  omega

end GoodReductionCardinality318
