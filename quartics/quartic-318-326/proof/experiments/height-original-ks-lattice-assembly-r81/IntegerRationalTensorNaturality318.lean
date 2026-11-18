module
public import IntegerTensorFieldSquares318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace IntegerRationalTensorNaturality318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
-- Scheme-facing coefficient base changes use the universe of the literal Z and Q.
variable {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
open IntegerTensorFieldSquares318

@[expose] def rationalCoefficient (A : Type) [CommRing A] : ℚ →+* Fiber A :=
  (Algebra.TensorProduct.includeRight : ℚ →ₐ[ℤ] Fiber A).toRingHom

theorem base_square :
    (rationalMap g).comp (algebraMap R (Fiber R)) =
      (algebraMap S (Fiber S)).comp g := by
  ext r
  exact rationalMap_base g r

theorem rational_square :
    (rationalMap g).comp (rationalCoefficient R) = rationalCoefficient S :=
  Subsingleton.elim _ _

abbrev intMap (A : Type) [CommRing A] :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ A))
abbrev rationalBaseMap := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))

/-- The actual categorical coefficient-base-change map induced by g. -/
@[expose] def baseChange : pullback (intMap S) rationalBaseMap ⟶
    pullback (intMap R) rationalBaseMap :=
  pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom g)) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id, intMap, ← Spec.map_comp]
      exact congrArg (fun f : ℤ →+* S => Spec.map (CommRingCat.ofHom f))
        (Subsingleton.elim (algebraMap ℤ S) (g.comp (algebraMap ℤ R))))
    (by simp)

/-- The literal localization-induced rationalMap is the map on the actual
Spec tensor pullbacks, with BOTH projections checked. -/
theorem tensor_naturality :
    Spec.map (CommRingCat.ofHom (rationalMap g)) ≫ (pullbackSpecIso ℤ R ℚ).inv =
      (pullbackSpecIso ℤ S ℚ).inv ≫ baseChange g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChange, pullback.map, pullback.lift_fst,
      pullbackSpecIso_inv_fst', pullbackSpecIso_inv_fst'_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : R →+* Fiber S => Spec.map (CommRingCat.ofHom f)) (base_square g)
  · simp only [Category.assoc, baseChange, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp]
    exact congrArg (fun f : ℚ →+* Fiber S => Spec.map (CommRingCat.ofHom f)) (rational_square g)

end IntegerRationalTensorNaturality318
