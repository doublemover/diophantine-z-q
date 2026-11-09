module
public import OriginalDescentBaseChangeComposition318
public section
noncomputable section
namespace AffineDescentCompositionComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDoubleNerve318 ActualAffineDescentData318
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R₀ S₀ R₁ S₁ R₂ S₂ : CommRingCat.{u})
  [Algebra R₀ S₀] [Algebra R₁ S₁] [Algebra R₂ S₂]
  (a₁ : Spec S₁ ⟶ Spec S₀) (b₁ : Spec R₁ ⟶ Spec R₀)
  (h₁ : a₁ ≫ baseMap R₀ S₀ = baseMap R₁ S₁ ≫ b₁)
  (a₂ : Spec S₂ ⟶ Spec S₁) (b₂ : Spec R₂ ⟶ Spec R₁)
  (h₂ : a₂ ≫ baseMap R₁ S₁ = baseMap R₂ S₂ ≫ b₂) (D : Datum R₀ S₀)

abbrev successive := OriginalSchemeDescentData318.toAffine R₂ S₂
  (OriginalDescentBaseChangeComposition318.successive (baseMap R₀ S₀) (baseMap R₁ S₁) (baseMap R₂ S₂)
    a₁ b₁ h₁ a₂ b₂ h₂ (OriginalSchemeDescentData318.ofAffine R₀ S₀ D))
abbrev direct := OriginalSchemeDescentData318.toAffine R₂ S₂
  (OriginalDescentBaseChangeComposition318.direct (baseMap R₀ S₀) (baseMap R₁ S₁) (baseMap R₂ S₂)
    a₁ b₁ h₁ a₂ b₂ h₂ (OriginalSchemeDescentData318.ofAffine R₀ S₀ D))

@[expose] def hom : Hom (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)
    (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D) where
  sheafHom := (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app D.line.object
  commutes := (OriginalDescentBaseChangeComposition318.hom
    (baseMap R₀ S₀) (baseMap R₁ S₁) (baseMap R₂ S₂) a₁ b₁ h₁ a₂ b₂ h₂
      (OriginalSchemeDescentData318.ofAffine R₀ S₀ D)).commutes

@[expose] def inv : Hom (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)
    (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D) where
  sheafHom := (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).inv.app D.line.object
  commutes := (OriginalDescentBaseChangeComposition318.inv
    (baseMap R₀ S₀) (baseMap R₁ S₁) (baseMap R₂ S₂) a₁ b₁ h₁ a₂ b₂ h₂
      (OriginalSchemeDescentData318.ofAffine R₀ S₀ D)).commutes

variable [Module.FaithfullyFlat R₂ S₂]

/-- Successive and direct original base changes reconstruct isomorphic
base lines. The iso is descended from the original covering-line
pullback associator, whose overlap compatibility was proved above. -/
@[expose] def comparison :
    (ActualAffineDescendedMaps318.line (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).object ≅
      (ActualAffineDescendedMaps318.line (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).object :=
  ActualAffineDescendedMaps318.iso
    (hom R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)
    (inv R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)
    ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom_inv_id_app D.line.object)
    ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).inv_hom_id_app D.line.object)

lemma comparison_cover :
    (Scheme.Modules.pullback (baseMap R₂ S₂)).map
        (comparison R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D).hom ≫
      (ActualAffineDescendedMaps318.comparison (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).hom =
    (ActualAffineDescendedMaps318.comparison (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).hom ≫
      (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app D.line.object :=
  ActualAffineDescendedMaps318.map_commutes (hom R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)

/-- The actual covering-associator square determines this comparison
among all maps of the original reconstructed base lines. -/
lemma comparison_unique
    (k : (ActualAffineDescendedMaps318.line (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).object ⟶
      (ActualAffineDescendedMaps318.line (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).object)
    (hk : (Scheme.Modules.pullback (baseMap R₂ S₂)).map k ≫
        (ActualAffineDescendedMaps318.comparison (direct R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).hom =
      (ActualAffineDescendedMaps318.comparison (successive R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D)).hom ≫
        (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app D.line.object) :
    k = (comparison R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D).hom :=
  ActualAffineDescendedMaps318.map_unique (hom R₀ S₀ R₁ S₁ R₂ S₂ a₁ b₁ h₁ a₂ b₂ h₂ D) k hk
end AffineDescentCompositionComparison318
