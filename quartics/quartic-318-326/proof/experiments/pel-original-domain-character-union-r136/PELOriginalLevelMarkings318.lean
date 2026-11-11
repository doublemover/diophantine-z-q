module
public import PELPeriodTorsionPolarization318
public import RegularLeftModuleAutomorphisms318
public section
noncomputable section
namespace PELOriginalLevelMarkings318
open PELOriginalThreeTorsion318 PELThreeTorsionOrderAction318 PELOrderReductionThree318
open PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1200000
variable (τ : ℂ) (hτ : 0<τ.im)

/-- Automorphisms of the entire actual3-torsion group which commute with
EVERY original order action, not just scalar or norm-one-unit actions. -/
abbrev MarkingAutomorphisms := {f : torsion τ ≃+ torsion τ //
  ∀ a : order, ∀ x : torsion τ, f (torsionOrderEnd τ a x)=torsionOrderEnd τ a (f x)}

@[expose] def regularToOriginal (f : RegularLeftModuleAutomorphisms318.Automorphisms QuotientOrder) :
    MarkingAutomorphisms τ :=
  ⟨((torsionEquiv τ hτ).symm.trans f.val).trans (torsionEquiv τ hτ),by
    intro a x
    change torsionEquiv τ hτ (f.val ((torsionEquiv τ hτ).symm (torsionOrderEnd τ a x)))=
      torsionOrderEnd τ a (torsionEquiv τ hτ (f.val ((torsionEquiv τ hτ).symm x)))
    rw [PELPeriodTorsionPolarization318.inverse_action,f.property]
    exact original_action τ hτ a _⟩

@[expose] def originalToRegular (f : MarkingAutomorphisms τ) :
    RegularLeftModuleAutomorphisms318.Automorphisms QuotientOrder :=
  ⟨((torsionEquiv τ hτ).trans f.val).trans (torsionEquiv τ hτ).symm,by
    intro a b
    obtain ⟨a,rfl⟩ := moduloThree.mk'_surjective a
    apply (torsionEquiv τ hτ).injective
    change torsionEquiv τ hτ ((torsionEquiv τ hτ).symm
      (f.val (torsionEquiv τ hτ (moduloThree.mk' a*b))))=
      torsionEquiv τ hτ (moduloThree.mk' a*((torsionEquiv τ hτ).symm
        (f.val (torsionEquiv τ hτ b))))
    simp only [AddEquiv.apply_symm_apply,original_action,f.property]⟩

@[expose] def regularEquiv :
    RegularLeftModuleAutomorphisms318.Automorphisms QuotientOrder ≃ MarkingAutomorphisms τ where
  toFun := regularToOriginal τ hτ
  invFun := originalToRegular τ hτ
  left_inv f := by
    apply Subtype.ext
    apply AddEquiv.ext
    intro x
    change (torsionEquiv τ hτ).symm (torsionEquiv τ hτ
      (f.val ((torsionEquiv τ hτ).symm (torsionEquiv τ hτ x))))=f.val x
    simp only [AddEquiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    apply AddEquiv.ext
    intro x
    change torsionEquiv τ hτ ((torsionEquiv τ hτ).symm
      (f.val (torsionEquiv τ hτ ((torsionEquiv τ hτ).symm x))))=f.val x
    simp only [AddEquiv.apply_symm_apply]

/-- Every original-order-compatible level marking change is precisely right
multiplication by a UNIQUE unit of the literal original maximal-order quotient. -/
@[expose] def unitsEquiv : QuotientOrderˣ ≃ MarkingAutomorphisms τ :=
  (RegularLeftModuleAutomorphisms318.unitsEquiv QuotientOrder).trans (regularEquiv τ hτ)

theorem unitsEquiv_value (u : QuotientOrderˣ) (x : torsion τ) :
    (unitsEquiv τ hτ u).val x=
      torsionEquiv τ hτ ((torsionEquiv τ hτ).symm x*(u:QuotientOrder)) := rfl

include hτ in
theorem marking_automorphisms_card : Nat.card (MarkingAutomorphisms τ)=72 := by
  rw [← Nat.card_congr (unitsEquiv τ hτ)]
  exact PELActualLevelThreeQuotient318.actual_counts.2.2.1
end PELOriginalLevelMarkings318
