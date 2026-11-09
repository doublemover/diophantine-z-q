module
public import SheafPathTransport318
public section
noncomputable section
namespace SheafTransportIntertwiner318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- An actual sheaf-overlap intertwiner remains an intertwiner under the
original normalized pullback. Both endpoint comparison squares come from
the original naturality, not an added compatibility hypothesis. -/
lemma square {U X Y : Scheme.{u}} {M N : U.Modules} (h : M ⟶ N)
    (q : Y ⟶ X) (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U)
    (h₀ : q ≫ p₀ = v₀) (h₁ : q ≫ p₁ = v₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M)
    (b : (Scheme.Modules.pullback p₀).obj N ⟶ (Scheme.Modules.pullback p₁).obj N)
    (hab : a ≫ (Scheme.Modules.pullback p₁).map h =
      (Scheme.Modules.pullback p₀).map h ≫ b) :
    SheafPathTransport318.transport M q p₀ p₁ v₀ v₁ h₀ h₁ a ≫
      (Scheme.Modules.pullback v₁).map h =
    (Scheme.Modules.pullback v₀).map h ≫
      SheafPathTransport318.transport N q p₀ p₁ v₀ v₁ h₀ h₁ b := by
  let c₀ := PullbackPathComposition318.iso q p₀ v₀ h₀
  let c₁ := PullbackPathComposition318.iso q p₁ v₁ h₁
  have hleft := c₀.hom.naturality h
  have hright := c₁.hom.naturality h
  simp only [Functor.comp_map] at hleft hright
  apply (cancel_epi (c₀.hom.app M)).mp
  simp only [SheafPathTransport318.transport, Category.assoc, Iso.hom_inv_id_app_assoc]
  change (Scheme.Modules.pullback q).map a ≫ c₁.hom.app M ≫
      (Scheme.Modules.pullback v₁).map h =
    c₀.hom.app M ≫ (Scheme.Modules.pullback v₀).map h ≫ c₀.inv.app N ≫
      (Scheme.Modules.pullback q).map b ≫ c₁.hom.app N
  rw [← hright, ← Category.assoc (c₀.hom.app M), ← hleft]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, hab, Functor.map_comp]
  simp only [Category.assoc]
end SheafTransportIntertwiner318
