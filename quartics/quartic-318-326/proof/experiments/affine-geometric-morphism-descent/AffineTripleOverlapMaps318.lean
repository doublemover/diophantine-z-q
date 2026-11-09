module
public import AffineTripleCoactionCoordinates318
public section
noncomputable section
namespace AffineTripleOverlapMaps318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open AffineCechRings318 AffineTripleCoactionCoordinates318
open scoped ChangeOfRings
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)

/-- The original R action is restriction through the given R-algebra S. -/
local instance moduleR (M : ModuleCat.{u} S) : Module R M :=
  Module.compHom M (algebraMap R S)
local instance towerR (M : ModuleCat.{u} S) : IsScalarTower R S M :=
  IsScalarTower.of_compHom ..

/-- Normalize the actual scalar pullback of an overlap map to its named
vertex modules using the original scalar-composition comparisons. -/
@[expose] def edge (τ : first R S N ⟶ second R S N)
    (m : double R S ⟶ triple R S) (v w : S ⟶ triple R S)
    (hv : m.hom.comp (leftMap R S S).hom = v.hom)
    (hw : m.hom.comp (rightMap R S S).hom = w.hom) :
    vertexModule R S N v ⟶ vertexModule R S N w :=
  (ScalarExtensionComposition318.comparison (leftMap R S S).hom m.hom N v.hom hv).inv ≫
    (ModuleCat.extendScalars m.hom).map τ ≫
    (ScalarExtensionComposition318.comparison (rightMap R S S).hom m.hom N w.hom hw).hom

lemma edge_tmul (τ : first R S N ⟶ second R S N)
    (m : double R S ⟶ triple R S) (v w : S ⟶ triple R S)
    (hv : m.hom.comp (leftMap R S S).hom = v.hom)
    (hw : m.hom.comp (rightMap R S S).hom = w.hom) (z : triple R S) (n : N) :
    edge R S N τ m v w hv hw (z ⊗ₜ[S, v.hom] n) =
      (ScalarExtensionComposition318.comparison (rightMap R S S).hom m.hom N w.hom hw).hom
        (z ⊗ₜ[double R S, m.hom]
          (τ ((1 : double R S) ⊗ₜ[S, (leftMap R S S).hom] n))) := by
  change (ScalarExtensionComposition318.comparison (rightMap R S S).hom m.hom N w.hom hw).hom
    ((ModuleCat.extendScalars m.hom).map τ
      ((ScalarExtensionComposition318.comparison (leftMap R S S).hom m.hom N v.hom hv).inv _)) = _
  rw [ScalarExtensionComposition318.comparison_inv_tmul, ModuleCat.ExtendScalars.map_tmul]

abbrev edge12 (τ : first R S N ⟶ second R S N) :=
  edge R S N τ (map12 R S) (vertex1 R S) (vertex2 R S) (map12_left R S) (map12_right R S)
abbrev edge13 (τ : first R S N ⟶ second R S N) :=
  edge R S N τ (map13 R S) (vertex1 R S) (vertex3 R S) (map13_left R S) (map13_right R S)
abbrev edge23 (τ : first R S N ⟶ second R S N) :=
  edge R S N τ (map23 R S) (vertex2 R S) (vertex3 R S) (map23_left R S) (map23_right R S)

abbrev comonad := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).toComonad

lemma comultiplication_tmul (a : S) (n : N) :
    (comonad R S).δ.app N (a ⊗ₜ[R, algebraMap R S] n) =
      a ⊗ₜ[R, algebraMap R S] ((1 : S) ⊗ₜ[R, algebraMap R S] n) := rfl

lemma comonad_map_tmul (d : N ⟶ comonadObject R S N) (a : S) (n : N) :
    (comonad R S).toFunctor.map d (a ⊗ₜ[R, algebraMap R S] n) =
      a ⊗ₜ[R, algebraMap R S] (d n) := rfl

/-- The geometric triple-overlap cocycle, stated using actual scalar
pullback and its canonical named-path normalizations. -/
@[expose] def Cocycle (τ : first R S N ⟶ second R S N) : Prop :=
  edge12 R S N τ ≫ edge23 R S N τ = edge13 R S N τ
end AffineTripleOverlapMaps318
