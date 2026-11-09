module
public import CanonicalBaseChangePasting318
public section
noncomputable section
namespace SheafArrowBaseChangePasting318
open AlgebraicGeometry CategoryTheory
open SheafArrowBaseChange318 ActualDescentBaseChangeDiagram318 CanonicalBaseChangePasting318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {U₀ U₁ U₂ D₀ D₁ D₂ : Scheme.{u}}

lemma endpoint_eq (a : U₁ ⟶ U₀) (q : D₁ ⟶ D₀) (p : D₀ ⟶ U₀) (r : D₁ ⟶ U₁)
    (h : q ≫ p = r ≫ a) : endpoint a q p r h = (coverComparison p r q a h).symm := rfl

variable (a₁ : U₁ ⟶ U₀) (a₂ : U₂ ⟶ U₁) (q₁ : D₁ ⟶ D₀) (q₂ : D₂ ⟶ D₁)
  (p₀ : D₀ ⟶ U₀) (p₁ : D₁ ⟶ U₁) (p₂ : D₂ ⟶ U₂)
  (h₁ : q₁ ≫ p₀ = p₁ ≫ a₁) (h₂ : q₂ ≫ p₁ = p₂ ≫ a₂)

/-- Actual endpoint comparisons satisfy the original pasting square,
with the original associator on both scheme-map composites. -/
lemma endpoint_pasting (M : U₀.Modules) :
    (endpoint a₂ q₂ p₁ p₂ h₂).hom.app ((Scheme.Modules.pullback a₁).obj M) ≫
      (Scheme.Modules.pullback q₂).map ((endpoint a₁ q₁ p₀ p₁ h₁).hom.app M) ≫
        (PullbackPathComposition318.iso q₂ q₁ (q₂ ≫ q₁) rfl).hom.app
          ((Scheme.Modules.pullback p₀).obj M) =
    (Scheme.Modules.pullback p₂).map
        ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app M) ≫
      (endpoint (a₂ ≫ a₁) (q₂ ≫ q₁) p₀ p₂
        (square_composition p₀ p₁ p₂ q₁ a₁ h₁ q₂ a₂ h₂)).hom.app M := by
  simp only [endpoint_eq, Iso.symm_hom]
  apply (cancel_mono ((coverComparison p₀ p₂ (q₂ ≫ q₁) (a₂ ≫ a₁)
    (square_composition p₀ p₁ p₂ q₁ a₁ h₁ q₂ a₂ h₂)).hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [cover_pasting p₀ p₁ p₂ q₁ a₁ h₁ q₂ a₂ h₂ M]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc]

variable (r₀ : D₀ ⟶ U₀) (r₁ : D₁ ⟶ U₁) (r₂ : D₂ ⟶ U₂)
  (k₁ : q₁ ≫ r₀ = r₁ ≫ a₁) (k₂ : q₂ ≫ r₁ = r₂ ≫ a₂)

/-- Two successive changes of the original overlap agree with the direct
change through the canonical source-line pullback-composition comparison.
This proves the actual transition equation needed for iterated descent. -/
lemma overlap_pasting (M : U₀.Modules)
    (τ : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback r₀).obj M) :
    overlap a₂ q₂ ((Scheme.Modules.pullback a₁).obj M) p₁ r₁ p₂ r₂ h₂ k₂
        (overlap a₁ q₁ M p₀ r₀ p₁ r₁ h₁ k₁ τ) ≫
      (Scheme.Modules.pullback r₂).map
        ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app M) =
    (Scheme.Modules.pullback p₂).map
        ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app M) ≫
      overlap (a₂ ≫ a₁) (q₂ ≫ q₁) M p₀ r₀ p₂ r₂
        (square_composition p₀ p₁ p₂ q₁ a₁ h₁ q₂ a₂ h₂)
        (square_composition r₀ r₁ r₂ q₁ a₁ k₁ q₂ a₂ k₂) τ := by
  let Q := PullbackPathComposition318.iso q₂ q₁ (q₂ ≫ q₁) rfl
  let A := (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).app M
  let x₀ := (endpoint a₂ q₂ p₁ p₂ h₂).app ((Scheme.Modules.pullback a₁).obj M) ≪≫
    (Scheme.Modules.pullback q₂).mapIso ((endpoint a₁ q₁ p₀ p₁ h₁).app M)
  let x₁ := (endpoint a₂ q₂ r₁ r₂ k₂).app ((Scheme.Modules.pullback a₁).obj M) ≪≫
    (Scheme.Modules.pullback q₂).mapIso ((endpoint a₁ q₁ r₀ r₁ k₁).app M)
  let y₀ := (endpoint (a₂ ≫ a₁) (q₂ ≫ q₁) p₀ p₂
    (square_composition p₀ p₁ p₂ q₁ a₁ h₁ q₂ a₂ h₂)).app M
  let y₁ := (endpoint (a₂ ≫ a₁) (q₂ ≫ q₁) r₀ r₂
    (square_composition r₀ r₁ r₂ q₁ a₁ k₁ q₂ a₂ k₂)).app M
  let c₀ := (Scheme.Modules.pullback p₂).mapIso A
  let c₁ := (Scheme.Modules.pullback r₂).mapIso A
  have hx₀ : x₀ ≪≫ Q.app ((Scheme.Modules.pullback p₀).obj M) = c₀ ≪≫ y₀ := by
    apply Iso.ext
    exact endpoint_pasting a₁ a₂ q₁ q₂ p₀ p₁ p₂ h₁ h₂ M
  have hx₁ : x₁ ≪≫ Q.app ((Scheme.Modules.pullback r₀).obj M) = c₁ ≪≫ y₁ := by
    apply Iso.ext
    exact endpoint_pasting a₁ a₂ q₁ q₂ r₀ r₁ r₂ k₁ k₂ M
  have hn : x₀.hom ≫ (Scheme.Modules.pullback q₂).map ((Scheme.Modules.pullback q₁).map τ) ≫ x₁.inv =
      (x₀ ≪≫ Q.app ((Scheme.Modules.pullback p₀).obj M)).hom ≫
        (Scheme.Modules.pullback (q₂ ≫ q₁)).map τ ≫
          (x₁ ≪≫ Q.app ((Scheme.Modules.pullback r₀).obj M)).inv := by
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [← Q.hom.naturality_assoc τ, Iso.hom_inv_id_app_assoc]
  have h : (x₀.hom ≫ (Scheme.Modules.pullback q₂).map ((Scheme.Modules.pullback q₁).map τ) ≫ x₁.inv) ≫
      c₁.hom = c₀.hom ≫ y₀.hom ≫ (Scheme.Modules.pullback (q₂ ≫ q₁)).map τ ≫ y₁.inv := by
    rw [hn, hx₀, hx₁]
    simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [overlap, x₀, x₁, y₀, y₁, c₀, c₁, A, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using h
end SheafArrowBaseChangePasting318
