module
public import PELOriginalCongruenceKernel318
public section
noncomputable section
namespace PELActualPrincipalThreeQuotient318
open PELPrincipalOrderCoordinates318 PELOrderReductionThree318 PELJointNormOneAction318
open PELPrincipalThreeFreeAction318 PELFiniteNormOneGroup318
open PELOriginalCongruenceKernel318 PELGlobalUnitReductionSurjective318
set_option maxHeartbeats 1200000

/-- Reduction of the EXACT determinant-one group already acting on the
original holomorphic period family, not a replacement abstract group. -/
@[expose] def normOneReduction : normOneUnits →* normOne where
  toFun u := ⟨originalUnitReduction u.val,
    (mem_normOne _).mpr (norm_one_reduces u.val ((mem_normOneUnits _).mp u.property))⟩
  map_one' := Subtype.ext (map_one originalUnitReduction)
  map_mul' u v := Subtype.ext (map_mul originalUnitReduction u.val v.val)

theorem normOneReduction_surjective : Function.Surjective normOneReduction := by
  intro u
  obtain ⟨v,hv,hn⟩ := PELGlobalNormOneLevelLifts318.original_norm_one_lift u.val
    ((mem_normOne _).mp u.property)
  exact ⟨⟨v,(mem_normOneUnits _).mpr hn⟩,Subtype.ext hv⟩

theorem kernel_membership (u : normOneUnits) :
    u∈normOneReduction.ker ↔ u.val∈principalThree := by
  have hr : normOneReduction u=1 ↔ originalUnitReduction u.val=1 := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  change normOneReduction u=1 ↔ u.val∈normOneUnits ∧ u.val∈congruentOneThree
  rw [hr,reduction_one_iff_congruent]
  exact ⟨fun h => ⟨u.property,h⟩,fun h => h.2⟩

/-- Equality with the literal principal-three group pulled back to the
actual norm-one group supplies the missing original subgroup identification. -/
theorem kernel_eq_original : normOneReduction.ker=
    principalThree.comap normOneUnits.subtype := by
  ext u
  exact kernel_membership u

abbrev FineLevelQuotient := normOneUnits ⧸ normOneReduction.ker
@[expose] def quotientEquiv : FineLevelQuotient ≃* normOne :=
  QuotientGroup.quotientKerEquivOfSurjective normOneReduction normOneReduction_surjective

theorem quotientEquiv_mk (u : normOneUnits) :
    quotientEquiv (QuotientGroup.mk u)=normOneReduction u := rfl

theorem fine_level_card : Nat.card FineLevelQuotient=36 := by
  rw [Nat.card_congr quotientEquiv.toEquiv]
  exact normOne_card
end PELActualPrincipalThreeQuotient318
