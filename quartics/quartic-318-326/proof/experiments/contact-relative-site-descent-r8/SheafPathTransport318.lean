module
public import PullbackPathComposition318
public section
noncomputable section
namespace SheafPathTransport318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {U X Y Z : Scheme.{u}} (M : U.Modules)

/-- Transport an actual sheaf morphism along an actual scheme map, retaining
both canonical named-path comparisons at its endpoints. -/
@[expose] def transport (q : Y ⟶ X) (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U)
    (h₀ : q ≫ p₀ = v₀) (h₁ : q ≫ p₁ = v₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    (Scheme.Modules.pullback v₀).obj M ⟶ (Scheme.Modules.pullback v₁).obj M :=
  (PullbackPathComposition318.iso q p₀ v₀ h₀).inv.app M ≫
    (Scheme.Modules.pullback q).map a ≫
    (PullbackPathComposition318.iso q p₁ v₁ h₁).hom.app M

lemma identity (q : Y ⟶ X) (p : X ⟶ U) (v : Y ⟶ U) (h : q ≫ p = v) :
    transport M q p p v v h h (𝟙 _) = 𝟙 _ := by
  simp only [transport, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

lemma composition (q : Y ⟶ X) (p₀ p₁ p₂ : X ⟶ U) (v₀ v₁ v₂ : Y ⟶ U)
    (h₀ : q ≫ p₀ = v₀) (h₁ : q ≫ p₁ = v₁) (h₂ : q ≫ p₂ = v₂)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M)
    (b : (Scheme.Modules.pullback p₁).obj M ⟶ (Scheme.Modules.pullback p₂).obj M) :
    transport M q p₀ p₁ v₀ v₁ h₀ h₁ a ≫ transport M q p₁ p₂ v₁ v₂ h₁ h₂ b =
      transport M q p₀ p₂ v₀ v₂ h₀ h₂ (a ≫ b) := by
  simp only [transport, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Two successive normalized actual pullbacks equal the normalized
pullback along their named composite. This is derived from the original
pullback associativity theorem and original composition naturality. -/
lemma successive (q : Y ⟶ X) (r : Z ⟶ Y) (rq : Z ⟶ X) (hrq : r ≫ q = rq)
    (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U) (w₀ w₁ : Z ⟶ U)
    (hq₀ : q ≫ p₀ = v₀) (hq₁ : q ≫ p₁ = v₁)
    (hr₀ : r ≫ v₀ = w₀) (hr₁ : r ≫ v₁ = w₁)
    (hc₀ : rq ≫ p₀ = w₀) (hc₁ : rq ≫ p₁ = w₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    transport M r v₀ v₁ w₀ w₁ hr₀ hr₁
      (transport M q p₀ p₁ v₀ v₁ hq₀ hq₁ a) =
        transport M rq p₀ p₁ w₀ w₁ hc₀ hc₁ a := by
  let F := Scheme.Modules.pullback r
  let c := PullbackPathComposition318.iso r q rq hrq
  let x₀ := F.mapIso ((PullbackPathComposition318.iso q p₀ v₀ hq₀).app M) ≪≫
    (PullbackPathComposition318.iso r v₀ w₀ hr₀).app M
  let x₁ := F.mapIso ((PullbackPathComposition318.iso q p₁ v₁ hq₁).app M) ≪≫
    (PullbackPathComposition318.iso r v₁ w₁ hr₁).app M
  let d₀ := (PullbackPathComposition318.iso rq p₀ w₀ hc₀).app M
  let d₁ := (PullbackPathComposition318.iso rq p₁ w₁ hc₁).app M
  have hx₀ : x₀ = c.app ((Scheme.Modules.pullback p₀).obj M) ≪≫ d₀ :=
    Iso.ext (PullbackPathComposition318.assoc r q p₀ rq v₀ w₀ hrq hq₀ hc₀ hr₀ M).symm
  have hx₁ : x₁ = c.app ((Scheme.Modules.pullback p₁).obj M) ≪≫ d₁ :=
    Iso.ext (PullbackPathComposition318.assoc r q p₁ rq v₁ w₁ hrq hq₁ hc₁ hr₁ M).symm
  have h : x₀.inv ≫ F.map ((Scheme.Modules.pullback q).map a) ≫ x₁.hom =
      d₀.inv ≫ (Scheme.Modules.pullback rq).map a ≫ d₁.hom := by
    rw [hx₀, hx₁]
    simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [c.hom.naturality_assoc a, Iso.inv_hom_id_app_assoc]
  simpa only [transport, x₀, x₁, d₀, d₁, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using h
/-- Canonical sheaf transport respects an actual commuting square of
scheme maps. Both routes retain their original path normalizations. -/
lemma square {X' Y' : Scheme.{u}} (q : Y ⟶ X) (d : Y' ⟶ Y)
    (b : X' ⟶ X) (r : Y' ⟶ X') (hs : d ≫ q = r ≫ b)
    (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U) (w₀ w₁ : X' ⟶ U) (z₀ z₁ : Y' ⟶ U)
    (hq₀ : q ≫ p₀ = v₀) (hq₁ : q ≫ p₁ = v₁)
    (hb₀ : b ≫ p₀ = w₀) (hb₁ : b ≫ p₁ = w₁)
    (hd₀ : d ≫ v₀ = z₀) (hd₁ : d ≫ v₁ = z₁)
    (hr₀ : r ≫ w₀ = z₀) (hr₁ : r ≫ w₁ = z₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    transport M d v₀ v₁ z₀ z₁ hd₀ hd₁ (transport M q p₀ p₁ v₀ v₁ hq₀ hq₁ a) =
      transport M r w₀ w₁ z₀ z₁ hr₀ hr₁ (transport M b p₀ p₁ w₀ w₁ hb₀ hb₁ a) := by
  have hc₀ : (d ≫ q) ≫ p₀ = z₀ := by rw [Category.assoc, hq₀, hd₀]
  have hc₁ : (d ≫ q) ≫ p₁ = z₁ := by rw [Category.assoc, hq₁, hd₁]
  rw [successive M q d (d ≫ q) rfl p₀ p₁ v₀ v₁ z₀ z₁ hq₀ hq₁ hd₀ hd₁ hc₀ hc₁,
    successive M b r (d ≫ q) hs.symm p₀ p₁ w₀ w₁ z₀ z₁ hb₀ hb₁ hr₀ hr₁ hc₀ hc₁]
end SheafPathTransport318
