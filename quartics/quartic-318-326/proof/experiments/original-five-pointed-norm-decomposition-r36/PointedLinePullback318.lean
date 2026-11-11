module
public import PointedLineDeformation318
public section
noncomputable section
namespace PointedLinePullback318
open AlgebraicGeometry CategoryTheory PointedLineDeformation318
universe u
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X Y₀ Y : Scheme.{u}} (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (h : i ≫ f = f₀ ≫ j)
/-- The original pullback composition comparisons, with the original commuting
square in between. Neither the line nor its special-fiber map is replaced. -/
@[expose] def squareComparison :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i ≅
      Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback f₀ :=
  Scheme.Modules.pullbackComp i f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp f₀ j).symm
@[expose] def deformation (L : Deformation j) : Deformation i where
  line := LineSheafPullback318.line f L.line
  trivialization := (squareComparison i j f f₀ h).app L.line.object ≪≫
    (Scheme.Modules.pullback f₀).mapIso L.trivialization ≪≫
    IdentityCotangent318.pullbackUnitIso f₀
/-- The actual sheaf isomorphism pulls back and remains pointed, by naturality
of the exact comparison and the specified old special-fiber square. -/
@[expose] def pointedIso {L M : Deformation j} (e : PointedIso j L M) :
    PointedIso i (deformation i j f f₀ h L) (deformation i j f f₀ h M) where
  iso := (Scheme.Modules.pullback f).mapIso e.iso
  compatible := by
    let P := Scheme.Modules.pullback f₀
    let η := squareComparison i j f f₀ h
    change (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback f).map e.iso.hom) ≫
      (η.hom.app M.line.object ≫ P.map M.trivialization.hom ≫
        (IdentityCotangent318.pullbackUnitIso f₀).hom) =
      η.hom.app L.line.object ≫ P.map L.trivialization.hom ≫
        (IdentityCotangent318.pullbackUnitIso f₀).hom
    have hn := η.hom.naturality e.iso.hom
    change (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback f).map e.iso.hom) ≫
      η.hom.app M.line.object = η.hom.app L.line.object ≫
        P.map ((Scheme.Modules.pullback j).map e.iso.hom) at hn
    simp only [← Category.assoc]
    rw [hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, e.compatible]
/-- Actual pointed pullback on classes, before any Picard representability. -/
@[expose] def pullback : PointedLineDeformation318.Class j → PointedLineDeformation318.Class i :=
  Quotient.map (deformation i j f f₀ h) (fun _ _ ⟨e⟩ => ⟨pointedIso i j f f₀ h e⟩)
lemma pullback_classOf (L : Deformation j) :
    pullback i j f f₀ h (classOf j L) = classOf i (deformation i j f f₀ h L) := rfl
/-- The square commutes with the repository's EXISTING line-class pullback. -/
lemma forget_pullback (c : PointedLineDeformation318.Class j) :
    forget i (pullback i j f f₀ h c) = LineSheafPullback318.pullback f (forget j c) := by
  induction c using Quotient.inductionOn with
  | h L => rfl
end PointedLinePullback318
