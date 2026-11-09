module
public import SheafArrowBaseChange318
public section
noncomputable section
namespace OriginalSchemeDescentData318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualOverlapDiagram318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U : Scheme.{u}} (f : U ⟶ B) (L : Line U)
abbrev firstObject := (Scheme.Modules.pullback (first f)).obj L.object
abbrev secondObject := (Scheme.Modules.pullback (second f)).obj L.object
variable (τ : firstObject f L ⟶ secondObject f L)

abbrev edge01 := SheafPathTransport318.transport L.object (pair01 f) (first f) (second f)
  (vertex0 f) (vertex1 f) rfl rfl τ
abbrev edge12 := SheafPathTransport318.transport L.object (pair12 f) (first f) (second f)
  (vertex1 f) (vertex2 f) (middle_condition f).symm rfl τ
abbrev edge02 := SheafPathTransport318.transport L.object (pair02 f) (first f) (second f)
  (vertex0 f) (vertex2 f) (pair02_first f) (pair02_second f) τ

def Diagonal : Prop := SheafPathTransport318.transport L.object (diagonal f)
  (first f) (second f) (𝟙 U) (𝟙 U) (diagonal_first f) (diagonal_second f) τ = 𝟙 _
def Cocycle : Prop := edge01 f L τ ≫ edge12 f L τ = edge02 f L τ

/-- Original geometric line descent data for any scheme arrow, before
covering hypotheses or affine/tensor presentations. -/
structure Datum where
  line : Line U
  overlap : firstObject f line ⟶ secondObject f line
  diagonal : Diagonal f line overlap
  triple : Cocycle f line overlap

/-- The retained affine datum gives this same original geometric datum;
only the named Spec identity is reconciled with the categorical identity. -/
@[expose] def ofAffine (R S : CommRingCat.{u}) [Algebra R S]
    (D : ActualAffineDescentData318.Datum R S) : Datum (ActualAffineDoubleNerve318.baseMap R S) where
  line := D.line
  overlap := D.overlap
  diagonal := by
    simpa only [ActualAffineSheafData318.Diagonal, Diagonal, Spec.map_id] using D.diagonal
  triple := D.triple

/-- Conversely, no geometric equations are lost on returning to the
original affine consumer with its named Spec identity convention. -/
@[expose] def toAffine (R S : CommRingCat.{u}) [Algebra R S]
    (D : Datum (ActualAffineDoubleNerve318.baseMap R S)) : ActualAffineDescentData318.Datum R S where
  line := D.line
  overlap := D.overlap
  diagonal := by
    simpa only [ActualAffineSheafData318.Diagonal, Diagonal, Spec.map_id] using D.diagonal
  triple := D.triple
end OriginalSchemeDescentData318
