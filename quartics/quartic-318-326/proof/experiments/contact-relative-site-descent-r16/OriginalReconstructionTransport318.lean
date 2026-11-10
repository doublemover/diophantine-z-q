module
public import CoverComparisonRectangle318
public section
noncomputable section
namespace OriginalReconstructionTransport318
open AlgebraicGeometry CategoryTheory ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 3200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

lemma path_rectangle {X S₁ S₂ U₁ U₂ : Scheme.{u}}
    (p₁ : U₁ ⟶ S₁) (p₂ : U₂ ⟶ S₂) (a : S₂ ⟶ S₁) (a' : U₂ ⟶ U₁)
    (ha : a' ≫ p₁ = p₂ ≫ a)
    (s₁ : S₁ ⟶ X) (s₂ : S₂ ⟶ X) (hs : a ≫ s₁ = s₂)
    (r₁ : U₁ ⟶ X) (r₂ : U₂ ⟶ X) (h₁ : p₁ ≫ s₁ = r₁)
    (h₂ : p₂ ≫ s₂ = r₂) (hr : a' ≫ r₁ = r₂) (L : X.Modules) :
    (coverComparison p₁ p₂ a' a ha).hom.app ((Scheme.Modules.pullback s₁).obj L) ≫
      (Scheme.Modules.pullback p₂).map ((PullbackPathComposition318.iso a s₁ s₂ hs).hom.app L) ≫
        (PullbackPathComposition318.iso p₂ s₂ r₂ h₂).hom.app L =
    (Scheme.Modules.pullback a').map ((PullbackPathComposition318.iso p₁ s₁ r₁ h₁).hom.app L) ≫
      (PullbackPathComposition318.iso a' r₁ r₂ hr).hom.app L := by
  have hc : (a' ≫ p₁) ≫ s₁ = r₂ := by rw [Category.assoc,h₁,hr]
  have hl := PullbackPathComposition318.assoc a' p₁ s₁ (a' ≫ p₁) r₁ r₂ rfl h₁ hc hr L
  have ht := PullbackPathComposition318.assoc p₂ a s₁ (a' ≫ p₁) s₂ r₂ ha.symm hs hc h₂ L
  rw [PullbackSquareTarget318.cover_common p₁ p₂ a' a ha (a' ≫ p₁) rfl ha.symm]
  simp only [NatTrans.comp_app,Category.assoc]
  rw [← ht]
  simpa only [Category.assoc,Iso.inv_hom_id_app_assoc] using hl

variable {X S₁ S₂ T₁ T₂ U₁ U₂ B₁ B₂ : Scheme.{u}}
  (f₁ : S₁ ⟶ T₁) (f₂ : S₂ ⟶ T₂) (g₁ : U₁ ⟶ B₁) (g₂ : U₂ ⟶ B₂)
  (p₁ : U₁ ⟶ S₁) (q₁ : B₁ ⟶ T₁) (h₁ : p₁ ≫ f₁ = g₁ ≫ q₁)
  (p₂ : U₂ ⟶ S₂) (q₂ : B₂ ⟶ T₂) (h₂ : p₂ ≫ f₂ = g₂ ≫ q₂)
  (a : S₂ ⟶ S₁) (b : T₂ ⟶ T₁) (hs : a ≫ f₁ = f₂ ≫ b)
  (a' : U₂ ⟶ U₁) (b' : B₂ ⟶ B₁) (ho : a' ≫ g₁ = g₂ ≫ b')
  (ha : a' ≫ p₁ = p₂ ≫ a) (hb : b' ≫ q₁ = q₂ ≫ b)
  (s₁ : S₁ ⟶ X) (s₂ : S₂ ⟶ X) (hss : a ≫ s₁ = s₂)
  (r₁ : U₁ ⟶ X) (r₂ : U₂ ⟶ X) (hp₁ : p₁ ≫ s₁ = r₁)
  (hp₂ : p₂ ≫ s₂ = r₂) (hr : a' ≫ r₁ = r₂)
  (L : X.Modules) (M₁ : T₁.Modules) (M₂ : T₂.Modules)
  (t : (Scheme.Modules.pullback b).obj M₁ ⟶ M₂)
  (e₁ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback s₁).obj L)
  (e₂ : (Scheme.Modules.pullback f₂).obj M₂ ⟶ (Scheme.Modules.pullback s₂).obj L)

include ha in
/-- Transport a proved original reconstruction square through both actual
chart squares. The conclusion retains the original covering line and the
specified source paths; the only input law is the spectrum reconstruction law. -/
lemma reconstruction_square
    (he : (Scheme.Modules.pullback f₂).map t ≫ e₂ =
      (coverComparison f₁ f₂ a b hs).inv.app M₁ ≫
        (Scheme.Modules.pullback a).map e₁ ≫
          (PullbackPathComposition318.iso a s₁ s₂ hss).hom.app L) :
    (Scheme.Modules.pullback g₂).map
        ((coverComparison q₁ q₂ b' b hb).hom.app M₁ ≫ (Scheme.Modules.pullback q₂).map t) ≫
      (coverComparison f₂ g₂ p₂ q₂ h₂).inv.app M₂ ≫
        (Scheme.Modules.pullback p₂).map e₂ ≫
          (PullbackPathComposition318.iso p₂ s₂ r₂ hp₂).hom.app L =
    (coverComparison g₁ g₂ a' b' ho).inv.app ((Scheme.Modules.pullback q₁).obj M₁) ≫
      (Scheme.Modules.pullback a').map
        ((coverComparison f₁ g₁ p₁ q₁ h₁).inv.app M₁ ≫
          (Scheme.Modules.pullback p₁).map e₁ ≫
            (PullbackPathComposition318.iso p₁ s₁ r₁ hp₁).hom.app L) ≫
              (PullbackPathComposition318.iso a' r₁ r₂ hr).hom.app L := by
  have hc := CoverComparisonRectangle318.rectangle f₁ f₂ g₁ g₂ p₁ q₁ h₁ p₂ q₂ h₂
    a b hs a' b' ho ha hb M₁
  have hn := (coverComparison f₂ g₂ p₂ q₂ h₂).inv.naturality t
  have hm := (coverComparison p₁ p₂ a' a ha).hom.naturality e₁
  simp only [Functor.comp_map] at hn hm
  have hp := path_rectangle p₁ p₂ a a' ha s₁ s₂ hss r₁ r₂ hp₁ hp₂ hr L
  apply (cancel_epi ((Scheme.Modules.pullback a').map
    ((coverComparison f₁ g₁ p₁ q₁ h₁).hom.app M₁) ≫
      (coverComparison g₁ g₂ a' b' ho).hom.app ((Scheme.Modules.pullback q₁).obj M₁))).mp
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_app_assoc,
    PullbackSquareTarget318.map_hom_inv_assoc,Iso.hom_inv_id_app,Category.id_comp]
  rw [← Category.assoc ((Scheme.Modules.pullback g₂).map ((Scheme.Modules.pullback q₂).map t)),hn]
  simp only [Category.assoc]
  have hc' := congrArg (fun z => z ≫ (coverComparison f₂ g₂ p₂ q₂ h₂).inv.app
    ((Scheme.Modules.pullback b).obj M₁) ≫
      (Scheme.Modules.pullback p₂).map ((Scheme.Modules.pullback f₂).map t ≫ e₂) ≫
        (PullbackPathComposition318.iso p₂ s₂ r₂ hp₂).hom.app L) hc
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_app_assoc] at hc'
  rw [hc']
  have he' : (coverComparison f₁ f₂ a b hs).hom.app M₁ ≫
      (Scheme.Modules.pullback f₂).map t ≫ e₂ =
    (Scheme.Modules.pullback a).map e₁ ≫
      (PullbackPathComposition318.iso a s₁ s₂ hss).hom.app L := by
    rw [he]
    simp only [Iso.hom_inv_id_app_assoc]
  have he'' := congrArg (fun z =>
    (coverComparison p₁ p₂ a' a ha).hom.app ((Scheme.Modules.pullback f₁).obj M₁) ≫
      (Scheme.Modules.pullback p₂).map z ≫
        (PullbackPathComposition318.iso p₂ s₂ r₂ hp₂).hom.app L) he'
  simp only [Functor.map_comp,Category.assoc] at he''
  rw [he'']
  rw [← Category.assoc ((coverComparison p₁ p₂ a' a ha).hom.app ((Scheme.Modules.pullback f₁).obj M₁)),← hm]
  simp only [Category.assoc]
  rw [hp]
end OriginalReconstructionTransport318
