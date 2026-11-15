module
public import OriginalSectionTransport318
public import OriginalOpenPullbackSections318
public section
noncomputable section
namespace OriginalOpenImageUnit318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalSectionTransport318 OriginalOpenPullbackSections318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)

/-- The normalized original unit on its full open image is exactly the
inverse of the original whole-open sections comparison. -/
lemma inverse (s : Γ(M,j ''ᵁ ⊤)) :
    sectionsEquiv j M (pullTo j M (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤) s) = s := by
  have hu := congrArg (fun q => q.app (j ''ᵁ ⊤) s)
    (OriginalOpenLineRestrictionUnit318.restriction_unit_inverse j M)
  change ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).app (j ⁻¹ᵁ (j ''ᵁ ⊤))
    (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app (j ''ᵁ ⊤) s) =
      M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ ⊤))).op s at hu
  change ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).app ⊤
    (move _ (j.preimage_image_eq ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app (j ''ᵁ ⊤) s)) = s
  rw [← move_map,hu]
  change M.presheaf.map _ (M.presheaf.map _ s) = s
  rw [← Functor.map_comp_apply]
  have hm : ∀ k : op (j ''ᵁ ⊤) ⟶ op (j ''ᵁ ⊤), M.presheaf.map k s = s := by
    intro k
    have hk : k = 𝟙 _ := Subsingleton.elim _ _
    simp [hk]
  exact hm _

lemma recover (s : Γ((Scheme.Modules.pullback j).obj M,⊤)) :
    pullTo j M (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤) (sectionsEquiv j M s) = s := by
  apply (sectionsEquiv j M).injective
  exact inverse j M _
end OriginalOpenImageUnit318
