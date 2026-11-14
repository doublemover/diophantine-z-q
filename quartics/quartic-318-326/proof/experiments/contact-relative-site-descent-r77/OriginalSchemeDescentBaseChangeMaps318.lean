module
public import OriginalSchemeDescentBaseChange318
public section
noncomputable section
namespace OriginalSchemeDescentBaseChangeMaps318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318 OriginalSchemeDescentData318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U : Scheme.{u}} {f : U ⟶ B}

/-- Morphisms retain the original covering sheaf map and actual double square. -/
structure Hom (D E : Datum f) where
  sheafHom : D.line.object ⟶ E.line.object
  commutes : D.overlap ≫ (Scheme.Modules.pullback (second f)).map sheafHom =
    (Scheme.Modules.pullback (first f)).map sheafHom ≫ E.overlap

@[ext] lemma Hom.ext {D E : Datum f} {h k : Hom D E}
    (he : h.sheafHom = k.sheafHom) : h = k := by
  cases h
  cases k
  cases he
  rfl

@[expose] def Hom.id (D : Datum f) : Hom D D where
  sheafHom := 𝟙 _
  commutes := by simp only [Functor.map_id, Category.comp_id, Category.id_comp]

@[expose] def Hom.comp {D E F : Datum f} (h : Hom D E) (k : Hom E F) : Hom D F where
  sheafHom := h.sheafHom ≫ k.sheafHom
  commutes := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, h.commutes,
      Category.assoc, k.commutes, Category.assoc]

variable {B' U' : Scheme.{u}} (g : U' ⟶ B') (a : U' ⟶ U) (b : B' ⟶ B)
  (square : a ≫ f = g ≫ b)

/-- Original compatible maps remain compatible after changing the actual
covering arrow. Endpoint compatibility follows from the original naturality. -/
@[expose] def map {D E : Datum f} (h : Hom D E) :
    Hom (OriginalSchemeDescentBaseChange318.datum f g a b square D)
      (OriginalSchemeDescentBaseChange318.datum f g a b square E) where
  sheafHom := (Scheme.Modules.pullback a).map h.sheafHom
  commutes := by
    let q := doubleMap f g a b square
    let c₀ := SheafArrowBaseChange318.endpoint a q (first f) (first g) (double_first f g a b square)
    let c₁ := SheafArrowBaseChange318.endpoint a q (second f) (second g) (double_second f g a b square)
    have hleft := c₀.hom.naturality h.sheafHom
    have hright := c₁.inv.naturality h.sheafHom
    simp only [Functor.comp_map] at hleft hright
    change c₀.hom.app D.line.object ≫ (Scheme.Modules.pullback q).map D.overlap ≫
        c₁.inv.app D.line.object ≫
          (Scheme.Modules.pullback (second g)).map ((Scheme.Modules.pullback a).map h.sheafHom) =
      (Scheme.Modules.pullback (first g)).map ((Scheme.Modules.pullback a).map h.sheafHom) ≫
        c₀.hom.app E.line.object ≫ (Scheme.Modules.pullback q).map E.overlap ≫ c₁.inv.app E.line.object
    rw [← hright, ← Functor.map_comp_assoc, h.commutes, Functor.map_comp]
    rw [← Category.assoc (c₀.hom.app D.line.object), ← hleft]
    simp only [Category.assoc]

lemma map_id (D : Datum f) : map g a b square (Hom.id D) =
    Hom.id (OriginalSchemeDescentBaseChange318.datum f g a b square D) :=
  Hom.ext ((Scheme.Modules.pullback a).map_id D.line.object)

lemma map_comp {D E F : Datum f} (h : Hom D E) (k : Hom E F) :
    map g a b square (h.comp k) = (map g a b square h).comp (map g a b square k) :=
  Hom.ext ((Scheme.Modules.pullback a).map_comp h.sheafHom k.sheafHom)
end OriginalSchemeDescentBaseChangeMaps318
