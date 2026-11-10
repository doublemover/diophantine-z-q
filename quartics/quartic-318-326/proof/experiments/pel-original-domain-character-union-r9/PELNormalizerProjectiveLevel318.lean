module
public import PELNormalizerInnerRelations318
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public section
noncomputable section
namespace PELNormalizerProjectiveLevel318
open PELOrderReductionThree318 PELNormalizerReductionAction318
set_option maxHeartbeats 1000000

@[expose] def unitConjugation (i : Fin 4) : QuotientOrderˣ ≃* QuotientOrderˣ :=
  Units.mapEquiv (quotientConjugation i).toMulEquiv

theorem unitConjugation_value (i : Fin 4) (u : QuotientOrderˣ) :
    (unitConjugation i u:QuotientOrder)=quotientConjugation i (u:QuotientOrder) := rfl

theorem unitConjugation_neg_one (i : Fin 4) : unitConjugation i (-1)= -1 := by
  apply Units.ext
  change quotientConjugation i (-1:QuotientOrder)= -1
  simp

/-- The actual central signs subgroup, not an arbitrary size2 subgroup, is
preserved by every one of the original normalizer conjugations. -/
theorem signs_preserved (i : Fin 4) :
    (LevelThreeKernel318.signs QuotientOrder).map (unitConjugation i).toMonoidHom=
      LevelThreeKernel318.signs QuotientOrder := by
  rw [LevelThreeKernel318.signs,MonoidHom.map_zpowers,unitConjugation_neg_one]

abbrev EffectiveLevel := QuotientOrderˣ ⧸ LevelThreeKernel318.signs QuotientOrder

/-- Genuine automorphisms of the original36-element projective unit quotient,
including p=3. They are induced by integral CONJUGATION, not nonunit multiplication. -/
@[expose] def effectiveConjugation (i : Fin 4) : EffectiveLevel ≃* EffectiveLevel :=
  QuotientGroup.congr _ _ (unitConjugation i) (signs_preserved i)

theorem effectiveConjugation_mk (i : Fin 4) (u : QuotientOrderˣ) :
    effectiveConjugation i (QuotientGroup.mk u)=QuotientGroup.mk (unitConjugation i u) := rfl

/-- The existing exact projective-unit count belongs to THIS quotient. -/
theorem effective_card : Nat.card EffectiveLevel=36 :=
  PELActualLevelThreeQuotient318.actual_counts.2.2.2
end PELNormalizerProjectiveLevel318
