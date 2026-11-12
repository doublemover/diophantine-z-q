module
public import PELOriginalThreeTorsion318
public section
noncomputable section
namespace PELThreeTorsionOrderAction318
open PELOriginalThirdPeriods318 PELOriginalThreeTorsion318 PELOrderReductionThree318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
set_option maxHeartbeats 1200000
variable (τ : ℂ)

/-- The original holomorphic order endomorphism preserves actual3-torsion. -/
@[expose] def torsionOrderEnd (a : order) : torsion τ →+ torsion τ where
  toFun x := ⟨orderEnd representation order τ a x,by
    change (3:ℤ) • orderEnd representation order τ a x.val=0
    rw [← map_zsmul,x.property,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem thirdVector_mul (a b : order) :
    thirdVector τ (a*b)=leftLinear (representation a) (thirdVector τ b) := by
  change (1/3:ℝ) • periodHom representation τ ((a:PELQuaternionAlgebra318.B)*b)=
    leftLinear (representation a) ((1/3:ℝ) • periodHom representation τ b)
  rw [periodHom_mul]
  exact ((leftLinear (representation a)).restrictScalars ℝ).map_smul
    (1/3:ℝ) (periodHom representation τ b) |>.symm

theorem thirdPeriod_mul (a b : order) :
    thirdPeriod τ (a*b)=orderEnd representation order τ a (thirdPeriod τ b) := by
  change quotientMap τ (thirdVector τ (a*b))=
    orderEnd representation order τ a (quotientMap τ (thirdVector τ b))
  rw [thirdVector_mul] <;> rfl

/-- The full marking intertwines the original order action with left regular
multiplication on O/3O. Every class, not just the four basis classes, is covered. -/
theorem original_action (hτ : 0<τ.im) (a : order) (b : QuotientOrder) :
    torsionEquiv τ hτ (moduloThree.mk' a*b)=
      torsionOrderEnd τ a (torsionEquiv τ hτ b) := by
  obtain ⟨b,rfl⟩ := moduloThree.mk'_surjective b
  rw [← map_mul]
  apply Subtype.ext
  exact thirdPeriod_mul τ a b

/-- Transported regular action is an explicit endomorphism of the actual
3-torsion group, and the preceding theorem identifies every original O action. -/
@[expose] def quotientAction (hτ : 0<τ.im) (a : QuotientOrder) : torsion τ →+ torsion τ where
  toFun x := torsionEquiv τ hτ (a*(torsionEquiv τ hτ).symm x)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

theorem quotientAction_original (hτ : 0<τ.im) (a : order) :
    quotientAction τ hτ (moduloThree.mk' a)=torsionOrderEnd τ a := by
  apply AddMonoidHom.ext
  intro x
  exact (original_action τ hτ a ((torsionEquiv τ hτ).symm x)).trans
    (congrArg (torsionOrderEnd τ a) ((torsionEquiv τ hτ).apply_symm_apply x))

theorem quotientAction_one (hτ : 0<τ.im) (x : torsion τ) :
    quotientAction τ hτ 1 x=x := by simp [quotientAction]

theorem quotientAction_mul (hτ : 0<τ.im) (a b : QuotientOrder) (x : torsion τ) :
    quotientAction τ hτ (a*b) x=quotientAction τ hτ a (quotientAction τ hτ b x) := by
  simp [quotientAction,mul_assoc]

theorem quotientAction_add (hτ : 0<τ.im) (a b : QuotientOrder) (x : torsion τ) :
    quotientAction τ hτ (a+b) x=quotientAction τ hτ a x+quotientAction τ hτ b x := by
  simp [quotientAction,add_mul]

theorem quotientAction_faithful (hτ : 0<τ.im) :
    Function.Injective (quotientAction τ hτ) := by
  intro a b hab
  have h := congrArg (fun f : torsion τ →+ torsion τ => f (torsionEquiv τ hτ 1)) hab
  apply (torsionEquiv τ hτ).injective
  simpa [quotientAction] using h

/-- This is a genuine left O/3O regular-module marking of the full actual
3-torsion. Algebraic/Tate realization and the normalizer extension are separate. -/
theorem original_full_level (hτ : 0<τ.im) :
    Nat.card (torsion τ)=81 ∧ Function.Injective (quotientAction τ hτ) ∧
      ∀ a : order, quotientAction τ hτ (moduloThree.mk' a)=torsionOrderEnd τ a :=
  ⟨torsion_card τ hτ,quotientAction_faithful τ hτ,quotientAction_original τ hτ⟩
end PELThreeTorsionOrderAction318
