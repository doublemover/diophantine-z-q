module
public import OriginalDescentBaseChangeComposition318
public section
noncomputable section
namespace OriginalDescentBaseChangePath318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OriginalSchemeDescentData318
variable {B₀ B₁ B₂ U₀ U₁ U₂ : Scheme.{u}}
  (f₀ : U₀ ⟶ B₀) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ U₀) (b₁ : B₁ ⟶ B₀) (h₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
  (a₂ : U₂ ⟶ U₁) (b₂ : B₂ ⟶ B₁) (h₂ : a₂ ≫ f₁ = f₂ ≫ b₂)
  (a₃ : U₂ ⟶ U₀) (b₃ : B₂ ⟶ B₀) (h₃ : a₃ ≫ f₀ = f₂ ≫ b₃)
  (ha : a₂ ≫ a₁ = a₃) (hb : b₂ ≫ b₁ = b₃) (D : Datum f₀)

/-- Successive restriction and the original named direct chart have the
same descent data via the actual pullback path, including endpoint transports. -/
@[expose] def hom : OriginalSchemeDescentBaseChangeMaps318.Hom
    (OriginalSchemeDescentBaseChange318.datum f₁ f₂ a₂ b₂ h₂
      (OriginalSchemeDescentBaseChange318.datum f₀ f₁ a₁ b₁ h₁ D))
    (OriginalSchemeDescentBaseChange318.datum f₀ f₂ a₃ b₃ h₃ D) where
  sheafHom := ((PullbackPathComposition318.iso a₂ a₁ a₃ ha).app D.line.object).hom
  commutes := by
    subst a₃
    subst b₃
    exact (OriginalDescentBaseChangeComposition318.hom f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D).commutes

@[expose] def inv : OriginalSchemeDescentBaseChangeMaps318.Hom
    (OriginalSchemeDescentBaseChange318.datum f₀ f₂ a₃ b₃ h₃ D)
    (OriginalSchemeDescentBaseChange318.datum f₁ f₂ a₂ b₂ h₂
      (OriginalSchemeDescentBaseChange318.datum f₀ f₁ a₁ b₁ h₁ D)) where
  sheafHom := ((PullbackPathComposition318.iso a₂ a₁ a₃ ha).app D.line.object).inv
  commutes := by
    subst a₃
    subst b₃
    exact (OriginalDescentBaseChangeComposition318.inv f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D).commutes

end OriginalDescentBaseChangePath318
