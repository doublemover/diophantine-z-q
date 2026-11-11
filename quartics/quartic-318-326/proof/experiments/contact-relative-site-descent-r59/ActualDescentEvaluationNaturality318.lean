module
public import ActualDescentTestEvaluation318
public section
noncomputable section
namespace ActualDescentEvaluationNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ActualOverlapDiagram318
open OriginalSchemeDescentData318 ActualDescentTestDiagram318 ActualDescentTestEvaluation318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y T T' : Scheme.{u}} {f : X ⟶ Y} (D : Datum f)
  (x y : T ⟶ X) (h : x ≫ f = y ≫ f)

lemma pair_pullback (r : T' ⟶ T) : r ≫ pair f x y h =
    pair f (r ≫ x) (r ≫ y) (by rw [Category.assoc,Category.assoc,h]) := by
  apply pullback.hom_ext
  · rw [Category.assoc,pair_first,pair_first]
  · rw [Category.assoc,pair_second,pair_second]

/-- Pulling back the evaluated original overlap uses exactly the old
pullback associators at both endpoints. -/
lemma pullback (r : T' ⟶ T) :
    SheafPathTransport318.transport D.line.object r x y (r ≫ x) (r ≫ y) rfl rfl (map D x y h) =
      map D (r ≫ x) (r ≫ y) (by rw [Category.assoc,Category.assoc,h]) :=
  SheafPathTransport318.successive D.line.object (pair f x y h) r
    (pair f (r ≫ x) (r ≫ y) (by rw [Category.assoc,Category.assoc,h]))
    (pair_pullback x y h r) (first f) (second f) x y (r ≫ x) (r ≫ y)
    (pair_first f x y h) (pair_second f x y h) rfl rfl
    (pair_first f (r ≫ x) (r ≫ y) _) (pair_second f (r ≫ x) (r ≫ y) _) D.overlap

variable {D}
/-- Every original descent-data map intertwines every evaluated pair,
with the same original sheaf map on both endpoints. -/
lemma natural {E : Datum f} (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E) :
    map D x y h ≫ (Scheme.Modules.pullback y).map k.sheafHom =
      (Scheme.Modules.pullback x).map k.sheafHom ≫ map E x y h := by
  let q := pair f x y h
  let c₀ := PullbackPathComposition318.iso q (first f) x (pair_first f x y h)
  let c₁ := PullbackPathComposition318.iso q (second f) y (pair_second f x y h)
  have h₀ := c₀.inv.naturality k.sheafHom
  have h₁ := c₁.hom.naturality k.sheafHom
  simp only [Functor.comp_map] at h₀ h₁
  change c₀.inv.app D.line.object ≫ (Scheme.Modules.pullback q).map D.overlap ≫
      c₁.hom.app D.line.object ≫ (Scheme.Modules.pullback y).map k.sheafHom =
    (Scheme.Modules.pullback x).map k.sheafHom ≫ c₀.inv.app E.line.object ≫
      (Scheme.Modules.pullback q).map E.overlap ≫ c₁.hom.app E.line.object
  rw [← h₁,← Functor.map_comp_assoc,k.commutes,Functor.map_comp]
  rw [← Category.assoc (c₀.inv.app D.line.object),← h₀]
  simp only [Category.assoc]
end ActualDescentEvaluationNaturality318
