module
public import OriginalOpenImageUnit318
public import OriginalCoefficientChartLine318
public section
noncomputable section
namespace OriginalWholeOpenCoefficientSquare318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalSectionTransport318 OriginalOpenPullbackSections318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y A B : Scheme.{0}} (p : Y ⟶ X) (j : A ⟶ X) (k : B ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k] (a : B ⟶ A) (h : a ≫ j = k ≫ p)
  (hp : p ⁻¹ᵁ (j ''ᵁ ⊤) = k ''ᵁ ⊤) (M : X.Modules)

@[expose] def comparison := (Scheme.Modules.pullbackComp a j).app M ≪≫
  (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp k p).app M).symm

/-- The exact affine/open-image square on ALL sections, with the actual
pullback associator and original ambient unit. No frame or cohomology
comparison is assumed. -/
lemma square (s : Γ((Scheme.Modules.pullback j).obj M,⊤)) :
    sectionsEquiv k ((Scheme.Modules.pullback p).obj M)
      ((comparison p j k a h M).hom.app ⊤
        (OriginalSectionPullbackComposition318.pull a ((Scheme.Modules.pullback j).obj M) s)) =
      pullTo p M (j ''ᵁ ⊤) (k ''ᵁ ⊤) hp (sectionsEquiv j M s) := by
  let t := sectionsEquiv j M s
  have haj : (a ≫ j) ⁻¹ᵁ (j ''ᵁ ⊤) = ⊤ := by
    rw [Scheme.Hom.comp_preimage,j.preimage_image_eq,Scheme.Hom.preimage_top]
  have hkp : (k ≫ p) ⁻¹ᵁ (j ''ᵁ ⊤) = ⊤ := by
    rw [Scheme.Hom.comp_preimage,hp,k.preimage_image_eq]
  have hA := OriginalSectionTransport318.composition a j M (j ''ᵁ ⊤) ⊤ ⊤
    (j.preimage_image_eq ⊤) (Scheme.Hom.preimage_top a) haj t
  have hB := OriginalSectionTransport318.composition k p M (j ''ᵁ ⊤) (k ''ᵁ ⊤) ⊤
    hp (k.preimage_image_eq ⊤) hkp t
  have hC := OriginalSectionTransport318.congr h M (j ''ᵁ ⊤) ⊤ haj hkp t
  have hs := OriginalOpenImageUnit318.recover j M s
  have htop : pullTo a ((Scheme.Modules.pullback j).obj M) ⊤ ⊤
      (Scheme.Hom.preimage_top a) s =
      OriginalSectionPullbackComposition318.pull a ((Scheme.Modules.pullback j).obj M) s := by
    simp [pullTo,move,OriginalSectionPullbackComposition318.pull]
  rw [show pullTo j M (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤) t = s from hs,htop] at hA
  have hc : (comparison p j k a h M).hom.app ⊤
      (OriginalSectionPullbackComposition318.pull a ((Scheme.Modules.pullback j).obj M) s) =
      pullTo k ((Scheme.Modules.pullback p).obj M) (k ''ᵁ ⊤) ⊤
        (k.preimage_image_eq ⊤) (pullTo p M (j ''ᵁ ⊤) (k ''ᵁ ⊤) hp t) := by
    change ((Scheme.Modules.pullbackComp k p).inv.app M).app ⊤
      (((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
        (((Scheme.Modules.pullbackComp a j).hom.app M).app ⊤ _)) = _
    rw [hA,hC,← hB]
    exact congrArg (fun q => q.app ⊤
      (pullTo k ((Scheme.Modules.pullback p).obj M) (k ''ᵁ ⊤) ⊤
        (k.preimage_image_eq ⊤) (pullTo p M (j ''ᵁ ⊤) (k ''ᵁ ⊤) hp t)))
      ((Scheme.Modules.pullbackComp k p).hom_inv_id_app M)
  rw [hc]
  exact OriginalOpenImageUnit318.inverse k ((Scheme.Modules.pullback p).obj M) _
end OriginalWholeOpenCoefficientSquare318
