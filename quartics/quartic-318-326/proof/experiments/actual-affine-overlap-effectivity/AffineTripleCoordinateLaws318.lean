module
public import AffineTripleOverlapMaps318
public section
noncomputable section
namespace AffineTripleCoordinateLaws318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open AffineCechRings318 AffineTripleCoactionCoordinates318 AffineTripleOverlapMaps318
open scoped ChangeOfRings
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)

/-- The original R action is restriction through the given R-algebra S. -/
local instance moduleR (M : ModuleCat.{u} S) : Module R M :=
  Module.compHom M (algebraMap R S)
local instance towerR (M : ModuleCat.{u} S) : IsScalarTower R S M :=
  IsScalarTower.of_compHom ..

/-- Pullback on the 13 edge inserts the middle unit, exactly the original
comonad comultiplication after the original double-overlap comparison. -/
lemma coordinates_lift13 (x : second R S N) :
    (coordinates R S N).hom
      ((ScalarExtensionComposition318.comparison (rightMap R S S).hom (map13 R S).hom
        N (vertex3 R S).hom (map13_right R S)).hom
        ((1 : triple R S) ⊗ₜ[double R S, (map13 R S).hom] x)) =
      (comonad R S).δ.app N ((component R S S N).hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z n =>
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
          rw [ScalarExtensionComposition318.comparison_tmul, one_mul,
            map13_tmul, coordinates_tmul, component_tmul, comultiplication_tmul]
      | add z w hz hw => simp only [add_tmul, tmul_add, map_add, hz, hw]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Pullback on the 23 edge preserves the first coordinate and applies
exactly the original double-overlap comparison in the other coordinates. -/
lemma coordinates_lift23 (a b : S) (x : second R S N) :
    (coordinates R S N).hom
      ((ScalarExtensionComposition318.comparison (rightMap R S S).hom (map23 R S).hom
        N (vertex3 R S).hom (map23_right R S)).hom
        ((a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) ⊗ₜ[double R S, (map23 R S).hom] x)) =
      a ⊗ₜ[R, algebraMap R S] (b • ((component R S S N).hom x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul z n =>
      induction z using TensorProduct.inductionOn with
      | tmul c d =>
          rw [ScalarExtensionComposition318.comparison_tmul, map23_tmul]
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [coordinates_tmul, component_tmul]
          change (a ⊗ₜ[R] ((b * c) ⊗ₜ[R] (d • n)) : S ⊗[R] (S ⊗[R] N)) =
            a ⊗ₜ[R] (b • (c ⊗ₜ[R] (d • n)))
          simp only [smul_tmul', smul_eq_mul]
      | add z w hz hw => simp only [add_tmul, tmul_add, map_add, smul_add, hz, hw]
  | add x y hx hy => simp only [tmul_add, map_add, smul_add, hx, hy]

lemma coordinates_edge23_tmul (τ : first R S N ⟶ second R S N)
    (a b : S) (n : N) :
    (coordinates R S N).hom
      (edge23 R S N τ ((a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) ⊗ₜ[S, (vertex2 R S).hom] n)) =
      a ⊗ₜ[R, algebraMap R S] (homEquiv R S N τ (b • n)) := by
  rw [edge_tmul, coordinates_lift23, ← homEquiv_value, map_smul]

/-- The 12-then-23 edge composite is the actual comonad map of the candidate
coaction, applied to the actual first coaction value. -/
lemma coordinates_edge23_lift12 (τ : first R S N ⟶ second R S N) (x : second R S N) :
    (coordinates R S N).hom
      (edge23 R S N τ
        ((ScalarExtensionComposition318.comparison (rightMap R S S).hom (map12 R S).hom
          N (vertex2 R S).hom (map12_right R S)).hom
          ((1 : triple R S) ⊗ₜ[double R S, (map12 R S).hom] x))) =
      (comonad R S).toFunctor.map (homEquiv R S N τ) ((component R S S N).hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z n =>
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
          rw [ScalarExtensionComposition318.comparison_tmul, one_mul, map12_tmul,
            coordinates_edge23_tmul, component_tmul, comonad_map_tmul]
      | add z w hz hw => simp only [add_tmul, tmul_add, map_add, hz, hw]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
end AffineTripleCoordinateLaws318
