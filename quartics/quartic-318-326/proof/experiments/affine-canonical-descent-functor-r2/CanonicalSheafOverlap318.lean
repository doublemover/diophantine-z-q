module
public import SheafIsoTransport318
public import ActualOverlapDiagram318
public section
noncomputable section
namespace CanonicalSheafOverlap318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U D T : Scheme.{u}} (M : B.Modules) (f : U ⟶ B)

/-- Canonical geometric overlap of an original pulled-back sheaf,
retaining the original common base map and both named path isomorphisms. -/
@[expose] def overlap (p₀ p₁ : D ⟶ U) (b : D ⟶ B)
    (h₀ : p₀ ≫ f = b) (h₁ : p₁ ≫ f = b) :
    (Scheme.Modules.pullback p₀).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback f).obj M) :=
  (PullbackPathComposition318.iso p₀ f b h₀).hom.app M ≫
    (PullbackPathComposition318.iso p₁ f b h₁).inv.app M

/-- Actual pullback preserves the canonical overlap, with precisely the
original associator at both endpoints. No overlap compatibility is assumed. -/
lemma transport (q : T ⟶ D) (p₀ p₁ : D ⟶ U) (b : D ⟶ B)
    (h₀ : p₀ ≫ f = b) (h₁ : p₁ ≫ f = b)
    (v₀ v₁ : T ⟶ U) (c : T ⟶ B)
    (hq₀ : q ≫ p₀ = v₀) (hq₁ : q ≫ p₁ = v₁)
    (hv₀ : v₀ ≫ f = c) (hv₁ : v₁ ≫ f = c) (hb : q ≫ b = c) :
    SheafPathTransport318.transport ((Scheme.Modules.pullback f).obj M)
      q p₀ p₁ v₀ v₁ hq₀ hq₁ (overlap M f p₀ p₁ b h₀ h₁) =
        overlap M f v₀ v₁ c hv₀ hv₁ := by
  have ha₀ := PullbackPathComposition318.assoc q p₀ f v₀ b c hq₀ h₀ hv₀ hb M
  have ha₁ := PullbackPathComposition318.assoc q p₁ f v₁ b c hq₁ h₁ hv₁ hb M
  apply (cancel_mono ((PullbackPathComposition318.iso v₁ f c hv₁).hom.app M)).mp
  simp only [SheafPathTransport318.transport, overlap, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [ha₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [← ha₀, Iso.inv_hom_id_app_assoc]

/-- Canonical overlap on the genuine original categorical double fiber
product, not a tensor-spectrum replacement. -/
@[expose] def actual :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first f)).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second f)).obj ((Scheme.Modules.pullback f).obj M) :=
  overlap M f (ActualOverlapDiagram318.first f) (ActualOverlapDiagram318.second f)
    (ActualOverlapDiagram318.first f ≫ f) rfl (ActualOverlapDiagram318.edge_condition f).symm
end CanonicalSheafOverlap318
