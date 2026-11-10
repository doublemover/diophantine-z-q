module
public import SheafPathTransport318
public section
noncomputable section
namespace SheafIsoTransport318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Original module-sheaf pullback along a scheme isomorphism reflects
actual morphism equality. The inverse is witnessed by the original
pullback composition, equality transport and identity comparison. -/
lemma pullback_injective {X Y : Scheme.{u}} (e : Y ≅ X) {M N : X.Modules}
    {f g : M ⟶ N} (h : (Scheme.Modules.pullback e.hom).map f =
      (Scheme.Modules.pullback e.hom).map g) : f = g := by
  let c : Scheme.Modules.pullback e.hom ⋙ Scheme.Modules.pullback e.inv ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId X
  have hh := congrArg (fun k => (Scheme.Modules.pullback e.inv).map k ≫ c.hom.app N) h
  have hf := c.hom.naturality f
  have hg := c.hom.naturality g
  simp only [Functor.comp_map, Functor.id_map] at hf hg
  rw [hf, hg] at hh
  exact (cancel_epi (c.hom.app M)).mp hh

/-- Canonical endpoint normalization preserves the equality-reflection
property of pullback along the actual scheme isomorphism. -/
lemma transport_injective {U X Y : Scheme.{u}} (M : U.Modules) (e : Y ≅ X)
    (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U)
    (h₀ : e.hom ≫ p₀ = v₀) (h₁ : e.hom ≫ p₁ = v₁)
    {a b : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M}
    (h : SheafPathTransport318.transport M e.hom p₀ p₁ v₀ v₁ h₀ h₁ a =
      SheafPathTransport318.transport M e.hom p₀ p₁ v₀ v₁ h₀ h₁ b) : a = b := by
  apply pullback_injective e
  have hh := congrArg (fun k =>
    (PullbackPathComposition318.iso e.hom p₀ v₀ h₀).hom.app M ≫ k ≫
      (PullbackPathComposition318.iso e.hom p₁ v₁ h₁).inv.app M) h
  simpa only [SheafPathTransport318.transport, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id] using hh

/-- Changing the original cover sheaf through a specified isomorphism
commutes with the normalized actual pullback of its overlap map. -/
lemma conjugation {U X Y : Scheme.{u}} {M N : U.Modules} (e : M ≅ N)
    (q : Y ⟶ X) (p₀ p₁ : X ⟶ U) (v₀ v₁ : Y ⟶ U)
    (h₀ : q ≫ p₀ = v₀) (h₁ : q ≫ p₁ = v₁)
    (a : (Scheme.Modules.pullback p₀).obj M ⟶ (Scheme.Modules.pullback p₁).obj M) :
    SheafPathTransport318.transport N q p₀ p₁ v₀ v₁ h₀ h₁
      ((Scheme.Modules.pullback p₀).map e.inv ≫ a ≫ (Scheme.Modules.pullback p₁).map e.hom) =
      (Scheme.Modules.pullback v₀).map e.inv ≫
        SheafPathTransport318.transport M q p₀ p₁ v₀ v₁ h₀ h₁ a ≫
        (Scheme.Modules.pullback v₁).map e.hom := by
  let c₀ := PullbackPathComposition318.iso q p₀ v₀ h₀
  let c₁ := PullbackPathComposition318.iso q p₁ v₁ h₁
  have hleft := c₀.inv.naturality e.inv
  have hright := c₁.hom.naturality e.hom
  simp only [Functor.comp_map] at hleft hright
  simp only [SheafPathTransport318.transport, Functor.map_comp, Category.assoc]
  change c₀.inv.app N ≫ (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback p₀).map e.inv) ≫
      (Scheme.Modules.pullback q).map a ≫
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback p₁).map e.hom) ≫ c₁.hom.app N = _
  rw [hright, ← Category.assoc (c₀.inv.app N), ← hleft]
  simp only [Category.assoc]
end SheafIsoTransport318
