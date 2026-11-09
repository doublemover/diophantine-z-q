module
public import OpenTraceSheaf318
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.Limits

public section
noncomputable section
namespace StructureAdditiveSheaf318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

abbrev additiveForget : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The original structure sheaf, regarded as a genuine additive sheaf. -/
@[expose, reducible] def sheaf (X : Scheme.{u}) : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨X.presheaf ⋙ additiveForget,
    CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.sheaf.property⟩

/-- The original direct image structure sheaf, not source cohomology by definition. -/
@[expose, reducible] def pushed {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  ⟨(f.base _* X.presheaf) ⋙ additiveForget,
    CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf f.base X.sheaf.property)⟩

/-- The actual structure-sheaf map of the original scheme morphism. -/
@[expose] def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : sheaf Y ⟶ pushed f :=
  ⟨Functor.whiskerRight f.c additiveForget⟩

theorem pullback_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (s : Γ(Y, U)) :
    (pullback f).hom.app (op U) s = f.app U s := rfl

/-- The object is exactly the ordinary topological sheaf pushforward. -/
theorem pushed_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushed f = (TopCat.Sheaf.pushforward AddCommGrpCat f.base).obj (sheaf X) := rfl

end StructureAdditiveSheaf318
