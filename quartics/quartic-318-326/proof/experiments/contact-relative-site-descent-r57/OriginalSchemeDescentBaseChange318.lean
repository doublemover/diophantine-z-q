module
public import OriginalSchemeDescentData318
public section
noncomputable section
namespace OriginalSchemeDescentBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318 OriginalSchemeDescentData318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (square : a ≫ f = g ≫ b) (D : Datum f)

variable {f} in
abbrev line := LineSheafPullback318.line a D.line

/-- The original overlap is pulled back along the actual categorical
map of doubles, with both original endpoint path comparisons retained. -/
@[expose] def overlap : firstObject g (line a D) ⟶ secondObject g (line a D) :=
  SheafArrowBaseChange318.overlap a (doubleMap f g a b square) D.line.object
    (first f) (second f) (first g) (second g)
    (double_first f g a b square) (double_second f g a b square) D.overlap

lemma edge01_eq : edge01 g (line a D) (overlap f g a b square D) =
    SheafArrowBaseChange318.overlap a (tripleMap f g a b square) D.line.object
      (vertex0 f) (vertex1 f) (vertex0 g) (vertex1 g)
      (triple_vertex0 f g a b square) (triple_vertex1 f g a b square)
      (edge01 f D.line D.overlap) :=
  SheafArrowBaseChange318.edge_square a (doubleMap f g a b square) D.line.object
    (first f) (second f) (first g) (second g)
    (double_first f g a b square) (double_second f g a b square)
    (pair01 f) (pair01 g) (tripleMap f g a b square) (triple_pair01 f g a b square).symm
    (vertex0 f) (vertex1 f) (vertex0 g) (vertex1 g) rfl rfl rfl rfl
    (triple_vertex0 f g a b square) (triple_vertex1 f g a b square) D.overlap

lemma edge12_eq : edge12 g (line a D) (overlap f g a b square D) =
    SheafArrowBaseChange318.overlap a (tripleMap f g a b square) D.line.object
      (vertex1 f) (vertex2 f) (vertex1 g) (vertex2 g)
      (triple_vertex1 f g a b square) (triple_vertex2 f g a b square)
      (edge12 f D.line D.overlap) :=
  SheafArrowBaseChange318.edge_square a (doubleMap f g a b square) D.line.object
    (first f) (second f) (first g) (second g)
    (double_first f g a b square) (double_second f g a b square)
    (pair12 f) (pair12 g) (tripleMap f g a b square) (triple_pair12 f g a b square).symm
    (vertex1 f) (vertex2 f) (vertex1 g) (vertex2 g)
    (middle_condition f).symm rfl (middle_condition g).symm rfl
    (triple_vertex1 f g a b square) (triple_vertex2 f g a b square) D.overlap

lemma edge02_eq : edge02 g (line a D) (overlap f g a b square D) =
    SheafArrowBaseChange318.overlap a (tripleMap f g a b square) D.line.object
      (vertex0 f) (vertex2 f) (vertex0 g) (vertex2 g)
      (triple_vertex0 f g a b square) (triple_vertex2 f g a b square)
      (edge02 f D.line D.overlap) :=
  SheafArrowBaseChange318.edge_square a (doubleMap f g a b square) D.line.object
    (first f) (second f) (first g) (second g)
    (double_first f g a b square) (double_second f g a b square)
    (pair02 f) (pair02 g) (tripleMap f g a b square) (triple_pair02 f g a b square).symm
    (vertex0 f) (vertex2 f) (vertex0 g) (vertex2 g)
    (pair02_first f) (pair02_second f) (pair02_first g) (pair02_second g)
    (triple_vertex0 f g a b square) (triple_vertex2 f g a b square) D.overlap

/-- The original actual triple law survives changing the covering arrow.
It is obtained by transporting the original equality, not assumed anew. -/
lemma triple : Cocycle g (line a D) (overlap f g a b square D) := by
  change edge01 g _ _ ≫ edge12 g _ _ = edge02 g _ _
  rw [edge01_eq, edge12_eq, edge02_eq, SheafArrowBaseChange318.overlap_composition]
  have hD : edge01 f D.line D.overlap ≫ edge12 f D.line D.overlap =
      edge02 f D.line D.overlap := D.triple
  rw [hD]

/-- The original actual diagonal law survives the same change of arrows. -/
lemma diagonal : Diagonal g (line a D) (overlap f g a b square D) := by
  have hi : a ≫ 𝟙 U = (𝟙 U') ≫ a := by rw [Category.comp_id, Category.id_comp]
  have h := SheafArrowBaseChange318.edge_square a (doubleMap f g a b square) D.line.object
    (first f) (second f) (first g) (second g)
    (double_first f g a b square) (double_second f g a b square)
    (ActualOverlapDiagram318.diagonal f) (ActualOverlapDiagram318.diagonal g) a
    (diagonal_double f g a b square) (𝟙 U) (𝟙 U) (𝟙 U') (𝟙 U')
    (diagonal_first f) (diagonal_second f) (diagonal_first g) (diagonal_second g) hi hi D.overlap
  change SheafPathTransport318.transport ((Scheme.Modules.pullback a).obj D.line.object)
      (ActualOverlapDiagram318.diagonal g) (first g) (second g) (𝟙 U') (𝟙 U')
      (diagonal_first g) (diagonal_second g) (overlap f g a b square D) = _ at h
  change _ = 𝟙 _
  have hD : SheafPathTransport318.transport D.line.object (ActualOverlapDiagram318.diagonal f)
      (first f) (second f) (𝟙 U) (𝟙 U) (diagonal_first f) (diagonal_second f) D.overlap = 𝟙 _ := D.diagonal
  rw [h, hD, SheafArrowBaseChange318.overlap_identity]

/-- Genuine original descent data pulls back along every commuting square
of scheme arrows. Neither cartesianness nor cover effectivity is silently
assumed; both actual geometric laws are proved above. -/
@[expose] def datum : Datum g where
  line := line a D
  overlap := overlap f g a b square D
  diagonal := diagonal f g a b square D
  triple := triple f g a b square D
end OriginalSchemeDescentBaseChange318
