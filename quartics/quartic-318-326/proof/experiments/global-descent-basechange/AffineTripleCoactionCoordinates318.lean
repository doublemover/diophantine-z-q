module
public import AffineCechRings318
public import ScalarExtensionComposition318
public import AffineOverlapCoaction318
public section
noncomputable section
namespace AffineTripleCoactionCoordinates318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open AffineCechRings318
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

abbrev vertexModule (v : S ⟶ triple R S) := (ModuleCat.extendScalars v.hom).obj N
abbrev twice := comonadObject R S (comonadObject R S N)

lemma base_left : algebraMap R (S ⊗[R] S) =
    (leftMap R S S).hom.comp (algebraMap R S) := by
  ext r
  exact IsScalarTower.algebraMap_apply R S (S ⊗[R] S) r

/-- Exact reconciliation of the original R action on the double-overlap
module with restriction through its first S factor. -/
@[expose] def restrictedComponent :
    (ModuleCat.restrictScalars (algebraMap R (S ⊗[R] S))).obj (second R S N) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj (comonadObject R S N) :=
  (ModuleCat.restrictScalarsComp' (algebraMap R S) (leftMap R S S).hom
      (algebraMap R (S ⊗[R] S)) (base_left R S)).app (second R S N) ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso (component R S S N)

/-- The actual third vertex module on S tensor (S tensor S) identifies with
the twice-applied original scalar-extension comonad. Every factor is a
canonical scalar-composition, restriction, or tensor-pushout comparison. -/
@[expose] def coordinates :
    (ModuleCat.restrictScalars (vertex1 R S).hom).obj
      (vertexModule R S N (vertex3 R S)) ≅ twice R S N :=
  (ModuleCat.restrictScalars (vertex1 R S).hom).mapIso
      (ScalarExtensionComposition318.comparison (rightMap R S S).hom
        (map23 R S).hom N (vertex3 R S).hom (map23_right R S)).symm ≪≫
    component R S (double R S) (second R S N) ≪≫
      (ModuleCat.extendScalars (algebraMap R S)).mapIso (restrictedComponent R S N)

/-- The comparison preserves the full tensor coordinates, not merely a
class label or a value at the generic point. -/
lemma coordinates_tmul (a b c : S) (n : N) :
    (coordinates R S N).hom
        ((a ⊗ₜ[R] (b ⊗ₜ[R] c)) ⊗ₜ[S, (vertex3 R S).hom] n) =
      a ⊗ₜ[R, algebraMap R S] (b ⊗ₜ[R, algebraMap R S] (c • n)) := by
  change (ModuleCat.extendScalars (algebraMap R S)).map (restrictedComponent R S N).hom
    ((component R S (double R S) (second R S N)).hom
      ((ScalarExtensionComposition318.comparison (rightMap R S S).hom
        (map23 R S).hom N (vertex3 R S).hom (map23_right R S)).inv _)) = _
  rw [ScalarExtensionComposition318.comparison_inv_tmul, component_tmul]
  change (ModuleCat.extendScalars (algebraMap R S)).map (restrictedComponent R S N).hom
    (a ⊗ₜ[R, algebraMap R S]
      ((b ⊗ₜ[R] c) • ((1 : S ⊗[R] S) ⊗ₜ[S, (rightMap R S S).hom] n))) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one, ModuleCat.ExtendScalars.map_tmul]
  change a ⊗ₜ[R, algebraMap R S]
    ((component R S S N).hom ((b ⊗ₜ[R] c) ⊗ₜ[S, (rightMap R S S).hom] n)) = _
  rw [component_tmul]
end AffineTripleCoactionCoordinates318
