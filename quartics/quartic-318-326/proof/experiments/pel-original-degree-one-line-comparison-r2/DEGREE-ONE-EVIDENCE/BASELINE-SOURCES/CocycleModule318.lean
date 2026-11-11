module
public import UnitTransitionCocycle318
public import OpenClutchedLine318
public import StructureUnitsSheaf318
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public section
noncomputable section
namespace CocycleModule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
@[expose] def chart (i:ι):X.Modules:=
  (Scheme.Modules.pushforward (U i).ι).obj (ClutchedModule318.unit (U i).toScheme)
@[expose] def overlap (i j:ι):X.Modules:=
  (Scheme.Modules.pushforward (OpenClutchedLine318.leftInclusion (U i) (U j)≫(U i).ι)).obj
    (ClutchedModule318.unit (U i⊓U j:X.Opens).toScheme)
@[expose] def left (i j:ι):chart U i⟶overlap U i j:=
  ClutchedModule318.restriction (U i).ι (OpenClutchedLine318.leftInclusion (U i) (U j))
@[expose] def right (i j:ι):chart U j⟶overlap U i j:=
  ClutchedModule318.twistedRestriction (U i).ι (U j).ι
    (OpenClutchedLine318.leftInclusion (U i) (U j))
    (OpenClutchedLine318.rightInclusion (U i) (U j))
    (OpenClutchedLine318.square (U i) (U j))
    (OpenClutchedLine318.transition (U i) (U j) (c.transition i j))
@[expose] def family:X.Modules:=∏ᶜ chart U
@[expose] def pairs:X.Modules:=∏ᶜ fun ij:ι×ι=>overlap U ij.1 ij.2
@[expose] def leftMap:family U⟶pairs U:=
  Pi.lift (fun ij=>Pi.π (chart U) ij.1≫left U ij.1 ij.2)
@[expose] def rightMap:family U⟶pairs U:=
  Pi.lift (fun ij=>Pi.π (chart U) ij.2≫right U c ij.1 ij.2)
/-- The actual O-module sheaf of compatible chart coefficients on the
specified arbitrary open family. Local freeness is not built into this definition. -/
@[expose] def object:X.Modules:=equalizer (leftMap U) (rightMap U c)
@[expose] def coefficient (i:ι):object U c⟶chart U i:=
  equalizer.ι _ _≫Pi.π (chart U) i
lemma compatible (i j:ι):coefficient U c i≫left U i j=
    coefficient U c j≫right U c i j:=by
  have h:=congrArg (fun g:object U c⟶pairs U=>g≫Pi.π (fun ij:ι×ι=>overlap U ij.1 ij.2) (i,j))
    (equalizer.condition (leftMap U) (rightMap U c))
  simpa only [coefficient,leftMap,rightMap,Category.assoc,Pi.lift_comp_π] using h
/-- Exact universal property for the original full-overlap compatibility maps. -/
@[expose] def lift {M:X.Modules} (s:∀i,M⟶chart U i)
    (h:∀i j,s i≫left U i j=s j≫right U c i j):M⟶object U c:=
  equalizer.lift (Pi.lift s) (by
    apply Pi.hom_ext
    intro ij
    simpa only [leftMap,rightMap,Category.assoc,Pi.lift_comp_π,Pi.lift_comp_π_assoc] using h ij.1 ij.2)
lemma lift_coefficient {M:X.Modules} (s:∀i,M⟶chart U i)
    (h:∀i j,s i≫left U i j=s j≫right U c i j) (i:ι):
    lift U c s h≫coefficient U c i=s i:=by
  simp only [lift,coefficient,←Category.assoc,equalizer.lift_ι,Pi.lift_comp_π]
lemma hom_ext {M:X.Modules} (a b:M⟶object U c)
    (h:∀i,a≫coefficient U c i=b≫coefficient U c i):a=b:=by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro i
  simpa only [coefficient,Category.assoc] using h i
end CocycleModule318
