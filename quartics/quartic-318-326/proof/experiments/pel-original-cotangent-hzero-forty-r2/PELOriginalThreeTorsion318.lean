module
public import PELOriginalThirdPeriods318
public section
noncomputable section
namespace PELOriginalThreeTorsion318
open PELOriginalThirdPeriods318 PELOrderReductionThree318
set_option maxHeartbeats 1200000
variable (τ : ℂ)

/-- The full additive3-torsion subgroup of the SAME original period quotient. -/
@[expose] def torsion : AddSubgroup (Torus τ) where
  carrier := {x | (3:ℤ) • x=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simpa [smul_add,hx,hy]
  neg_mem' := by intro x hx; simpa [smul_neg,hx]

@[expose] def orderToTorsion : PELPrincipalOrderCoordinates318.order →+ torsion τ where
  toFun a := ⟨thirdPeriod τ a,third_killed τ a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- Quotient descent uses the already proved literal congruence modulo3O. -/
@[expose] def quotientToTorsion (hτ : 0<τ.im) : QuotientOrder →+ torsion τ where
  toFun := Quotient.lift (orderToTorsion τ) (by
    intro a b hab
    apply Subtype.ext
    change thirdPeriod τ a=thirdPeriod τ b
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (third_kernel τ hτ (a-b)).mpr ((moduloThree_iff a b).mp hab))
  map_zero' := map_zero (orderToTorsion τ)
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (orderToTorsion τ) a b

theorem quotientToTorsion_mk (hτ : 0<τ.im) (a : PELPrincipalOrderCoordinates318.order) :
    quotientToTorsion τ hτ (moduloThree.mk' a)=orderToTorsion τ a := rfl

theorem quotientToTorsion_injective (hτ : 0<τ.im) :
    Function.Injective (quotientToTorsion τ hτ) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.sound
  apply (moduloThree_iff a b).mpr
  apply (third_kernel τ hτ (a-b)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hab)

theorem quotientToTorsion_surjective (hτ : 0<τ.im) :
    Function.Surjective (quotientToTorsion τ hτ) := by
  intro x
  obtain ⟨a,ha⟩ := third_surjective τ x.val x.property
  exact ⟨moduloThree.mk' a,Subtype.ext ha⟩

/-- Actual full level-three marking as an additive group, not merely a
cardinality equality or an abstract torsor of the right size. -/
@[expose] def torsionEquiv (hτ : 0<τ.im) : QuotientOrder ≃+ torsion τ :=
  AddEquiv.ofBijective (quotientToTorsion τ hτ)
    ⟨quotientToTorsion_injective τ hτ,quotientToTorsion_surjective τ hτ⟩

theorem torsion_card (hτ : 0<τ.im) : Nat.card (torsion τ)=81 := by
  rw [← Nat.card_congr (torsionEquiv τ hτ).toEquiv]
  exact PELActualLevelThreeQuotient318.quotient_card
end PELOriginalThreeTorsion318
