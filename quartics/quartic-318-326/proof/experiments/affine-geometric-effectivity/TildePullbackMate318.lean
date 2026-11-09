module
public import AffineGlobalSectionCoherence318
public section
noncomputable section
namespace TildePullbackMate318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ u

/-- Unit transposes determine the exact mate of a natural transformation. -/
lemma conjugate_of_transposes {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (h : ∀ X, b.homEquiv _ _ (α.app X) = a.unit.app X ≫ β.app (L₁.obj X)) :
    conjugateEquiv a b α = β := by
  apply (conjugateEquiv a b).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext X
  apply (b.homEquiv _ _).injective
  rw [h, Adjunction.homEquiv_unit]
  exact unit_conjugateEquiv_symm a b β X

/-- The comparison obtained by transporting the right adjoint and then
using left-adjoint uniqueness has the specified right comparison as its mate.
This fixes the actual comparison, including its normalization. -/
lemma conjugate_leftAdjointUniq {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₂ ≅ R₁) :
    conjugateEquiv a b ((b.ofNatIsoRight e).leftAdjointUniq a).hom = e.inv := by
  apply conjugate_of_transposes
  intro X
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (b.ofNatIsoRight e) a X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono (e.hom.app _)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The existing canonical tilde pullback comparison, with its original
adjunctions, is the mate of the inverse actual affine global-section map. -/
lemma comparison_mate :
    conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
      (TildePullback318.pullbackIso f).hom =
        (TildePullback318.globalNatIso f).inv :=
  conjugate_leftAdjointUniq _ _ _

lemma comparison_inverse_mate :
    conjugateEquiv
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
      (TildePullback318.pullbackIso f).inv =
        (TildePullback318.globalNatIso f).hom := by
  have h : conjugateIsoEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
      (TildePullback318.pullbackIso f) = (TildePullback318.globalNatIso f).symm :=
    Iso.ext (comparison_mate f)
  exact congrArg Iso.inv h
end TildePullbackMate318
