module
public import SheafArrowBaseChangePasting318
public section
noncomputable section
namespace OriginalDescentBaseChangeComposition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318 OriginalSchemeDescentData318
open CanonicalBaseChangePasting318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B₀ B₁ B₂ U₀ U₁ U₂ : Scheme.{u}}
  (f₀ : U₀ ⟶ B₀) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ U₀) (b₁ : B₁ ⟶ B₀) (h₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
  (a₂ : U₂ ⟶ U₁) (b₂ : B₂ ⟶ B₁) (h₂ : a₂ ≫ f₁ = f₂ ≫ b₂)

/-- The actual map on categorical doubles respects composition of the
original commuting squares, by the original pullback universal property. -/
lemma double_composition :
    doubleMap f₀ f₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
      (square_composition f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂) =
      doubleMap f₁ f₂ a₂ b₂ h₂ ≫ doubleMap f₀ f₁ a₁ b₁ h₁ := by
  apply pullback.hom_ext
  · rw [double_first, Category.assoc, double_first, ← Category.assoc, double_first, Category.assoc]
  · rw [double_second, Category.assoc, double_second, ← Category.assoc, double_second, Category.assoc]

variable (D : Datum f₀)
abbrev successive := OriginalSchemeDescentBaseChange318.datum f₁ f₂ a₂ b₂ h₂
  (OriginalSchemeDescentBaseChange318.datum f₀ f₁ a₁ b₁ h₁ D)
abbrev direct := OriginalSchemeDescentBaseChange318.datum f₀ f₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
  (square_composition f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂) D

variable {f₀} in
abbrev lineIso := (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).app D.line.object

/-- The original line pullback-composition iso is an actual descent-data
morphism from successive base change to direct base change. The overlap
square is proved from the original endpoint pasting theorem. -/
@[expose] def hom : OriginalSchemeDescentBaseChangeMaps318.Hom
    (successive f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D) (direct f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D) where
  sheafHom := (lineIso a₁ a₂ D).hom
  commutes := by
    have h := SheafArrowBaseChangePasting318.overlap_pasting a₁ a₂
      (doubleMap f₀ f₁ a₁ b₁ h₁) (doubleMap f₁ f₂ a₂ b₂ h₂)
      (first f₀) (first f₁) (first f₂)
      (double_first f₀ f₁ a₁ b₁ h₁) (double_first f₁ f₂ a₂ b₂ h₂)
      (second f₀) (second f₁) (second f₂)
      (double_second f₀ f₁ a₁ b₁ h₁) (double_second f₁ f₂ a₂ b₂ h₂) D.line.object D.overlap
    simpa only [successive, direct, OriginalSchemeDescentBaseChange318.datum,
      OriginalSchemeDescentBaseChange318.overlap, double_composition, lineIso] using h

/-- Compatibility of the original inverse line comparison is derived. -/
@[expose] def inv : OriginalSchemeDescentBaseChangeMaps318.Hom
    (direct f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D) (successive f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D) where
  sheafHom := (lineIso a₁ a₂ D).inv
  commutes := by
    let A := successive f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D
    let B := direct f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D
    let p := (Scheme.Modules.pullback (first f₂)).mapIso (lineIso a₁ a₂ D)
    let q := (Scheme.Modules.pullback (second f₂)).mapIso (lineIso a₁ a₂ D)
    have h : A.overlap ≫ q.hom = p.hom ≫ B.overlap := (hom f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ D).commutes
    change B.overlap ≫ q.inv = p.inv ≫ A.overlap
    apply (cancel_epi p.hom).mp
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
end OriginalDescentBaseChangeComposition318
