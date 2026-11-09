module
public import OriginalLocalRecoveryDescent318
public section
noncomputable section
namespace OriginalDescentSquareReflection318
open AlgebraicGeometry CategoryTheory
open OriginalSchemeDescentData318 ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (square : a ≫ f = g ≫ b)
  (D E : Datum f) (k : D.line.object ⟶ E.line.object)

/-- The exact endpoint normalizations reflect a local original descent
square into the pullback of the global square. No faithfulness assumption
is used until the separate full-double-cover detector is applied. -/
lemma pullback_square
    (h : (OriginalSchemeDescentBaseChange318.datum f g a b square D).overlap ≫
        (Scheme.Modules.pullback (second g)).map ((Scheme.Modules.pullback a).map k) =
      (Scheme.Modules.pullback (first g)).map ((Scheme.Modules.pullback a).map k) ≫
        (OriginalSchemeDescentBaseChange318.datum f g a b square E).overlap) :
    (Scheme.Modules.pullback (doubleMap f g a b square)).map
      (D.overlap ≫ (Scheme.Modules.pullback (second f)).map k) =
    (Scheme.Modules.pullback (doubleMap f g a b square)).map
      ((Scheme.Modules.pullback (first f)).map k ≫ E.overlap) := by
  let q := doubleMap f g a b square
  let c₀ := SheafArrowBaseChange318.endpoint a q (first f) (first g) (double_first f g a b square)
  let c₁ := SheafArrowBaseChange318.endpoint a q (second f) (second g) (double_second f g a b square)
  have hleft := c₀.hom.naturality k
  have hright := c₁.inv.naturality k
  simp only [Functor.comp_map] at hleft hright
  change c₀.hom.app D.line.object ≫ (Scheme.Modules.pullback q).map D.overlap ≫
      c₁.inv.app D.line.object ≫
        (Scheme.Modules.pullback (second g)).map ((Scheme.Modules.pullback a).map k) =
    (Scheme.Modules.pullback (first g)).map ((Scheme.Modules.pullback a).map k) ≫
      c₀.hom.app E.line.object ≫ (Scheme.Modules.pullback q).map E.overlap ≫
        c₁.inv.app E.line.object at h
  rw [← hright,← Category.assoc ((Scheme.Modules.pullback (first g)).map
    ((Scheme.Modules.pullback a).map k)),hleft] at h
  apply (cancel_epi c₀.hom.app D.line.object).mp
  apply (cancel_mono c₁.inv.app E.line.object).mp
  simpa only [Functor.map_comp,Category.assoc] using h
end OriginalDescentSquareReflection318
