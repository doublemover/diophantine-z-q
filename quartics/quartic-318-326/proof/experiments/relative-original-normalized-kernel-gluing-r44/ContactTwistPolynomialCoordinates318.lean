module
public import OriginalOpenUntwistLinear318
public import ContactPositiveGlobalGenerators318
public section
noncomputable section
namespace ContactTwistPolynomialCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open ContactRelativeWholeOpenSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)

/-- Untwisting preserves the actual polynomial chart action, not merely
the coefficient-R action. This is needed to consume the generator spans. -/
@[expose] def finite : finiteSections R c (twist R c L d) ≃ₗ[Polynomial R] finiteSections R c L where
  __ := (OriginalOpenUntwistLinear318.equivalence (CommRingCat.of (R ⊗[ℚ] finiteRing c))
    (finiteInto R c) (twist R c L d).object L.object
    (ContactRelativeTwistedCoordinates318.finiteCoordinates R c L d _ le_rfl)).toAddEquiv
  map_smul' p x :=
    (OriginalOpenUntwistLinear318.equivalence (CommRingCat.of (R ⊗[ℚ] finiteRing c))
      (finiteInto R c) (twist R c L d).object L.object
      (ContactRelativeTwistedCoordinates318.finiteCoordinates R c L d _ le_rfl)).map_smul
        (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (finiteRing c) p) x

@[expose] def infinity : infinitySections R c (twist R c L d) ≃ₗ[Polynomial R] infinitySections R c L where
  __ := (OriginalOpenUntwistLinear318.equivalence (CommRingCat.of (R ⊗[ℚ] infinityRing c))
    (infinityInto R c) (twist R c L d).object L.object
    (ContactRelativeTwistedCoordinates318.infinityCoordinates R c L d _ le_rfl)).toAddEquiv
  map_smul' p x :=
    (OriginalOpenUntwistLinear318.equivalence (CommRingCat.of (R ⊗[ℚ] infinityRing c))
      (infinityInto R c) (twist R c L d).object L.object
      (ContactRelativeTwistedCoordinates318.infinityCoordinates R c L d _ le_rfl)).map_smul
        (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c) p) x

lemma finite_apply (x : finiteSections R c (twist R c L d)) :
    finite R c L d x = ContactRelativeTwistKernel318.finiteCoordinates R c L d x := rfl
lemma infinity_apply (x : infinitySections R c (twist R c L d)) :
    infinity R c L d x = ContactRelativeTwistKernel318.infinityCoordinates R c L d x := rfl

/-- Transport spanning through this SPECIFIED polynomial-linear original
frame map. This does not infer generation from an arbitrary additive map. -/
lemma span_of_equiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (Polynomial R) A] [Module (Polynomial R) B]
    (e : A ≃ₗ[Polynomial R] B) {ι : Type*} (s : ι → A)
    (h : Submodule.span (Polynomial R) (Set.range (fun i => e (s i))) = ⊤) :
    Submodule.span (Polynomial R) (Set.range s) = ⊤ := by
  apply top_unique
  intro x hx
  have he : e x ∈ Submodule.span (Polynomial R) (Set.range (fun i => e (s i))) := by
    rw [h]; trivial
  have hmem (y : B) (hy : y ∈ Submodule.span (Polynomial R) (Set.range (fun i => e (s i)))) :
      e.symm y ∈ Submodule.span (Polynomial R) (Set.range s) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro y ⟨i,rfl⟩
      simpa only [LinearEquiv.symm_apply_apply] using
        (Submodule.subset_span (⟨i,rfl⟩ : s i ∈ Set.range s))
    · simpa only [map_zero] using (Submodule.span (Polynomial R) (Set.range s)).zero_mem
    · intro a b _ _ ha hb
      simpa only [map_add] using (Submodule.span (Polynomial R) (Set.range s)).add_mem ha hb
    · intro a b _ hb
      simpa only [map_smul] using (Submodule.span (Polynomial R) (Set.range s)).smul_mem a hb
  simpa only [LinearEquiv.symm_apply_apply] using hmem (e x) he
end ContactTwistPolynomialCoordinates318
