module
public import ActualAffineEffectiveComparison318
public import SheafTransportIntertwiner318
public import GeometricAffineDescendedFunctor318
public section
noncomputable section
namespace ActualAffineDescentData318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualAffineDoubleNerve318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Original affine geometric data on the genuine categorical scheme
fiber products. Tensor and coalgebra laws are consequences, not fields. -/
structure Datum where
  line : Line (Spec S)
  overlap : ActualAffineSheafData318.firstObject R S line ⟶
    ActualAffineSheafData318.secondObject R S line
  diagonal : ActualAffineSheafData318.Diagonal R S line overlap
  triple : ActualAffineSheafData318.Cocycle R S line overlap

variable {R S}
/-- Actual covering sheaf maps compatible with the original overlap on
the original categorical double. -/
structure Hom (D E : Datum R S) where
  sheafHom : D.line.object ⟶ E.line.object
  commutes : D.overlap ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map sheafHom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map sheafHom ≫ E.overlap

@[ext] lemma Hom.ext {D E : Datum R S} {h k : Hom D E}
    (e : h.sheafHom = k.sheafHom) : h = k := by
  cases h
  cases k
  cases e
  rfl

@[expose] def Hom.id (D : Datum R S) : Hom D D where
  sheafHom := 𝟙 _
  commutes := by simp only [Functor.map_id, Category.comp_id, Category.id_comp]

@[expose] def Hom.comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) : Hom D F where
  sheafHom := h.sheafHom ≫ k.sheafHom
  commutes := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, h.commutes,
      Category.assoc, k.commutes, Category.assoc]

/-- Exact conversion to the retained geometric tensor-spectrum datum. -/
@[expose] def tensorDatum (D : Datum R S) : GeometricAffineDescentData318.Datum R S where
  line := D.line
  overlap := ActualAffineTensorTransport318.overlap R S D.line D.overlap
  diagonal := ActualAffineTensorLaws318.diagonal R S D.line D.overlap D.diagonal
  triple := ActualAffineTensorLaws318.triple R S D.line D.overlap D.triple

/-- Original actual-double intertwiners supply the previous tensor
intertwiners through the original canonical comparison squares. -/
@[expose] def Hom.tensor {D E : Datum R S} (h : Hom D E) :
    GeometricAffineDescentData318.Hom (tensorDatum D) (tensorDatum E) where
  sheafHom := h.sheafHom
  commutes := SheafTransportIntertwiner318.square h.sheafHom (doubleIso R S).inv
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (Spec.map (AffineModuleBaseChange318.leftMap R S S))
    (Spec.map (AffineModuleBaseChange318.rightMap R S S))
    (inverse_first R S) (inverse_second R S) D.overlap E.overlap h.commutes

lemma Hom.tensor_id (D : Datum R S) : (Hom.id D).tensor =
    GeometricAffineDescentData318.Hom.id (tensorDatum D) :=
  GeometricAffineDescentData318.Hom.ext rfl
lemma Hom.tensor_comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) :
    (h.comp k).tensor = h.tensor.comp k.tensor :=
  GeometricAffineDescentData318.Hom.ext rfl
end ActualAffineDescentData318
