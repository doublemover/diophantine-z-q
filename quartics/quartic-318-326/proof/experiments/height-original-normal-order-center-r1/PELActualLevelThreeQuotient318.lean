module
public import PELReductionResidueField318
public section
noncomputable section
namespace PELActualLevelThreeQuotient318
open PELOrderReductionThree318 PELReductionResidueField318
set_option maxHeartbeats 1200000
noncomputable instance quotientFintype : Fintype QuotientOrder :=
  Fintype.ofEquiv Reduction quotientEquiv.symm.toEquiv

/-- Residue map on the literal quotient of the original maximal order. -/
@[expose] def quotientResidue : QuotientOrder →+* Residue :=
  residue.comp quotientEquiv.toRingHom

theorem quotientResidue_surjective : Function.Surjective quotientResidue :=
  residue_surjective.comp quotientEquiv.surjective

theorem quotientResidue_mk (x : PELPrincipalOrderCoordinates318.order) :
    quotientResidue (moduloThree.mk' x)=residue (reduction x) := rfl

theorem quotient_radical_square (x : QuotientOrder) (hx : quotientResidue x=0) : x^2=0 := by
  apply quotientEquiv.injective
  rw [map_pow,map_zero]
  exact radical_square_zero _ hx

theorem quotient_card : Nat.card QuotientOrder=81 := by
  rw [Nat.card_congr quotientEquiv.toEquiv]
  exact reduction_card

theorem quotient_two_ne_zero : (2:QuotientOrder)≠0 := by
  intro h
  apply PELReductionResidueField318.two_ne_zero
  simpa only [map_ofNat,map_zero] using congrArg quotientEquiv h

/-- The old level-kernel counting application now consumes the actual O/3O.
No arbitrary ring-model equivalence or supplied cardinality is an input. -/
theorem actual_counts : Nat.card QuotientOrder=81 ∧
    Nat.card quotientResidue.toAddMonoidHom.ker=9 ∧ Nat.card QuotientOrderˣ=72 ∧
      Nat.card (QuotientOrderˣ ⧸ LevelThreeKernel318.signs QuotientOrder)=36 := by
  exact ⟨quotient_card,
    LevelThreeKernel318.kernel_card quotientResidue quotientResidue_surjective
      quotient_card residue_card,
    LevelThreeKernel318.units_card quotientResidue quotientResidue_surjective
      quotient_radical_square quotient_card residue_card,
    LevelThreeKernel318.effective_kernel_card quotientResidue quotientResidue_surjective
      quotient_radical_square quotient_card residue_card quotient_two_ne_zero⟩

/-- The finite normalizer extension is STILL an actual geometric/group input.
This discharges only its quaternionic local-ring/counting prerequisite. -/
theorem actual_extension_card {Γ : Type*} [Group Γ]
    (q : Γ→*LevelThreeKernel318.W) (hq : Function.Surjective q)
    (e : q.ker≃*(QuotientOrderˣ ⧸ LevelThreeKernel318.signs QuotientOrder)) :
    Nat.card Γ=576 :=
  LevelThreeKernel318.extension_card quotientResidue quotientResidue_surjective
    quotient_radical_square quotient_card residue_card quotient_two_ne_zero q hq e
end PELActualLevelThreeQuotient318
