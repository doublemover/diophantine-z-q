module
public import SheafPathTransport318
public import ActualAffineTripleNerve318
public import OriginalGeometricAffineLine318
public section
noncomputable section
namespace ActualAffineSheafData318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualAffineDoubleNerve318
open ActualOverlapDiagram318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
abbrev firstObject := (Scheme.Modules.pullback (first (baseMap R S))).obj L.object
abbrev secondObject := (Scheme.Modules.pullback (second (baseMap R S))).obj L.object
variable (τ : firstObject R S L ⟶ secondObject R S L)

abbrev edge01 := SheafPathTransport318.transport L.object (pair01 (baseMap R S))
  (first (baseMap R S)) (second (baseMap R S)) (vertex0 (baseMap R S)) (vertex1 (baseMap R S))
  rfl rfl τ
abbrev edge12 := SheafPathTransport318.transport L.object (pair12 (baseMap R S))
  (first (baseMap R S)) (second (baseMap R S)) (vertex1 (baseMap R S)) (vertex2 (baseMap R S))
  (middle_condition (baseMap R S)).symm rfl τ
abbrev edge02 := SheafPathTransport318.transport L.object (pair02 (baseMap R S))
  (first (baseMap R S)) (second (baseMap R S)) (vertex0 (baseMap R S)) (vertex2 (baseMap R S))
  (pair02_first (baseMap R S)) (pair02_second (baseMap R S)) τ

/-- Genuine sheaf cocycle on the actual scheme fiber-product triple. -/
@[expose] def Cocycle : Prop := edge01 R S L τ ≫ edge12 R S L τ = edge02 R S L τ

/-- Genuine diagonal identity, normalized through canonical pullback paths
to the named Spec identity map. This is an equality of actual sheaf maps. -/
@[expose] def Diagonal : Prop :=
  SheafPathTransport318.transport L.object (ActualOverlapDiagram318.diagonal (baseMap R S))
    (first (baseMap R S)) (second (baseMap R S)) (Spec.map (𝟙 S)) (Spec.map (𝟙 S))
    ((diagonal_first (baseMap R S)).trans (Spec.map_id S).symm)
    ((diagonal_second (baseMap R S)).trans (Spec.map_id S).symm) τ = 𝟙 _
end ActualAffineSheafData318
