module
public import ActualDescentTestDiagram318
public section
noncomputable section
namespace ActualDescentTestEvaluation318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualOverlapDiagram318
open OriginalSchemeDescentData318 ActualDescentTestDiagram318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y T : Scheme.{u}} {f : X ⟶ Y} (D : Datum f)

/-- The input overlap evaluated on any actual pair over the base. -/
@[expose] def map (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    (Scheme.Modules.pullback x).obj D.line.object ⟶ (Scheme.Modules.pullback y).obj D.line.object :=
  SheafPathTransport318.transport D.line.object (pair f x y h) (first f) (second f) x y
    (pair_first f x y h) (pair_second f x y h) D.overlap

lemma self (x : T ⟶ X) : map D x x rfl = 𝟙 _ := by
  have he := SheafPathTransport318.successive D.line.object (diagonal f) x (pair f x x rfl)
    (diagonal_pair f x) (first f) (second f) (𝟙 X) (𝟙 X) x x
    (diagonal_first f) (diagonal_second f) (Category.comp_id x) (Category.comp_id x)
    (pair_first f x x rfl) (pair_second f x x rfl) D.overlap
  have hd : SheafPathTransport318.transport D.line.object (diagonal f) (first f) (second f)
    (𝟙 X) (𝟙 X) (diagonal_first f) (diagonal_second f) D.overlap = 𝟙 _ := D.diagonal
  rw [hd,SheafPathTransport318.identity] at he
  exact he.symm

variable (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f)

lemma edge01 : SheafPathTransport318.transport D.line.object (triple f x y z h k)
    (vertex0 f) (vertex1 f) x y (triple_vertex0 f x y z h k) (triple_vertex1 f x y z h k)
    (OriginalSchemeDescentData318.edge01 f D.line D.overlap) = map D x y h :=
  SheafPathTransport318.successive D.line.object (pair01 f) (triple f x y z h k) (pair f x y h)
    (triple_pair01 f x y z h k) (first f) (second f) (vertex0 f) (vertex1 f) x y rfl rfl
    (triple_vertex0 f x y z h k) (triple_vertex1 f x y z h k)
    (pair_first f x y h) (pair_second f x y h) D.overlap

lemma edge12 : SheafPathTransport318.transport D.line.object (triple f x y z h k)
    (vertex1 f) (vertex2 f) y z (triple_vertex1 f x y z h k) (triple_vertex2 f x y z h k)
    (OriginalSchemeDescentData318.edge12 f D.line D.overlap) = map D y z k :=
  SheafPathTransport318.successive D.line.object (pair12 f) (triple f x y z h k) (pair f y z k)
    (triple_pair12 f x y z h k) (first f) (second f) (vertex1 f) (vertex2 f) y z
    (middle_condition f).symm rfl (triple_vertex1 f x y z h k) (triple_vertex2 f x y z h k)
    (pair_first f y z k) (pair_second f y z k) D.overlap

lemma edge02 : SheafPathTransport318.transport D.line.object (triple f x y z h k)
    (vertex0 f) (vertex2 f) x z (triple_vertex0 f x y z h k) (triple_vertex2 f x y z h k)
    (OriginalSchemeDescentData318.edge02 f D.line D.overlap) = map D x z (h.trans k) :=
  SheafPathTransport318.successive D.line.object (pair02 f) (triple f x y z h k)
    (pair f x z (h.trans k)) (triple_pair02 f x y z h k) (first f) (second f)
    (vertex0 f) (vertex2 f) x z (pair02_first f) (pair02_second f)
    (triple_vertex0 f x y z h k) (triple_vertex2 f x y z h k)
    (pair_first f x z (h.trans k)) (pair_second f x z (h.trans k)) D.overlap

/-- The actual original triple equation gives composition on every test
scheme. This is derived, not a replacement cocycle premise. -/
lemma composition : map D x y h ≫ map D y z k = map D x z (h.trans k) := by
  rw [← edge01 D x y z h k,← edge12 D x y z h k,
    SheafPathTransport318.composition]
  have ht : OriginalSchemeDescentData318.edge01 f D.line D.overlap ≫
      OriginalSchemeDescentData318.edge12 f D.line D.overlap =
    OriginalSchemeDescentData318.edge02 f D.line D.overlap := D.triple
  rw [ht,edge02]

/-- The original geometric laws force each evaluated overlap to be an
isomorphism, with inverse the same input overlap on the reversed pair. -/
@[expose] def iso (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    (Scheme.Modules.pullback x).obj D.line.object ≅ (Scheme.Modules.pullback y).obj D.line.object where
  hom := map D x y h
  inv := map D y x h.symm
  hom_inv_id := by rw [composition,self]
  inv_hom_id := by rw [composition,self]
end ActualDescentTestEvaluation318
