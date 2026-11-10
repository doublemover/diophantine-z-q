module
public import OriginalAffineReconstructionUnit318
public section
noncomputable section
namespace ActualDescentBaseChangeDiagram318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualOverlapDiagram318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (square : a ≫ f = g ≫ b)

/-- The actual map on the original categorical double for a map of
covering arrows. No tensor-spectrum presentation is chosen. -/
@[expose] def doubleMap : Double g ⟶ Double f :=
  pullback.lift (first g ≫ a) (second g ≫ a) (by
    simp only [Category.assoc, square]
    rw [← Category.assoc, edge_condition, Category.assoc])

@[reassoc] lemma double_first : doubleMap f g a b square ≫ first f = first g ≫ a :=
  pullback.lift_fst _ _ _
@[reassoc] lemma double_second : doubleMap f g a b square ≫ second f = second g ≫ a :=
  pullback.lift_snd _ _ _

/-- The actual map on adjacent categorical triples is constructed by its
original pullback universal property and exact middle-face equation. -/
@[expose] def tripleMap : Triple g ⟶ Triple f :=
  pullback.lift (pair01 g ≫ doubleMap f g a b square) (pair12 g ≫ doubleMap f g a b square) (by
    rw [Category.assoc, Category.assoc, double_second, double_first,
      ← Category.assoc, ← Category.assoc, middle_condition])

@[reassoc] lemma triple_pair01 : tripleMap f g a b square ≫ pair01 f =
    pair01 g ≫ doubleMap f g a b square := pullback.lift_fst _ _ _
@[reassoc] lemma triple_pair12 : tripleMap f g a b square ≫ pair12 f =
    pair12 g ≫ doubleMap f g a b square := pullback.lift_snd _ _ _

@[reassoc] lemma triple_vertex0 : tripleMap f g a b square ≫ vertex0 f = vertex0 g ≫ a := by
  rw [vertex0, ← Category.assoc, triple_pair01, Category.assoc, double_first, ← Category.assoc]
@[reassoc] lemma triple_vertex1 : tripleMap f g a b square ≫ vertex1 f = vertex1 g ≫ a := by
  rw [vertex1, ← Category.assoc, triple_pair01, Category.assoc, double_second, ← Category.assoc]
@[reassoc] lemma triple_vertex2 : tripleMap f g a b square ≫ vertex2 f = vertex2 g ≫ a := by
  rw [vertex2, ← Category.assoc, triple_pair12, Category.assoc, double_second, ← Category.assoc]

/-- The omitted edge is preserved as the actual original pullback lift. -/
@[reassoc] lemma triple_pair02 : tripleMap f g a b square ≫ pair02 f =
    pair02 g ≫ doubleMap f g a b square := by
  apply pullback.hom_ext
  · rw [Category.assoc, pair02_first, triple_vertex0, Category.assoc, double_first,
      ← Category.assoc, pair02_first]
  · rw [Category.assoc, pair02_second, triple_vertex2, Category.assoc, double_second,
      ← Category.assoc, pair02_second]

/-- The original diagonal is preserved, with the actual covering-arrow map. -/
@[reassoc] lemma diagonal_double : diagonal g ≫ doubleMap f g a b square = a ≫ diagonal f := by
  apply pullback.hom_ext
  · rw [Category.assoc, double_first, ← Category.assoc, diagonal_first,
      Category.id_comp, Category.assoc, diagonal_first, Category.comp_id]
  · rw [Category.assoc, double_second, ← Category.assoc, diagonal_second,
      Category.id_comp, Category.assoc, diagonal_second, Category.comp_id]

/-- The actual canonical covering-object base-change comparison. This
comparison exists for every commuting square, before any covering or
cartesian hypothesis is asserted. -/
@[expose] def coverComparison :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback g :=
  PullbackPathComposition318.iso a f (g ≫ b) square ≪≫
    (PullbackPathComposition318.iso g b (g ≫ b) rfl).symm

lemma coverComparison_natural {M N : B.Modules} (h : M ⟶ N) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map h) ≫
        (coverComparison f g a b square).hom.app N =
      (coverComparison f g a b square).hom.app M ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map h) :=
  (coverComparison f g a b square).hom.naturality h
end ActualDescentBaseChangeDiagram318
