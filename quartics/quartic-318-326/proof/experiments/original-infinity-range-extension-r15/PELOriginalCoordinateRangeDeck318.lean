module
public import PELOriginalRegularCoordinateAlgebra318
public import Mathlib.AlgebraicGeometry.Scheme
public section
noncomputable section
namespace PELOriginalCoordinateRangeDeck318
open AlgebraicGeometry CategoryTheory
open PELOriginalRegularCoordinateAlgebra318 PELOriginalMaximalQuotient318

/-- Literal original-coordinate subalgebra INSIDE genuine functions on
RegularSource. No injectivity of evaluation is assumed in this definition. -/
abbrev OriginalAlgebra := evaluation.range

/-- Precomposition by the actual original point action, not a transported
model-field automorphism. The inverse uses the same original inverse label. -/
@[expose] def functionDeck (w : Labels) : Functions ≃ₐ[ℂ] Functions where
  toFun f x := f (originalAction w x)
  invFun f x := f (originalAction w⁻¹ x)
  left_inv f := by
    funext x
    apply congrArg f
    apply Subtype.ext
    exact smul_inv_smul w x.val
  right_inv f := by
    funext x
    apply congrArg f
    apply Subtype.ext
    exact inv_smul_smul w x.val
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

lemma evaluation_deck (w : Labels) (a : CoordinateRing) :
    evaluation (FourRootCoordinateRingSigns318.finiteEnd
      PELOriginalCommonContactBase318.branches (OriginalContactInertiaBasis318.basis w) a) =
      functionDeck w (evaluation a) := by
  funext x
  exact (AlgHom.congr_fun (deck_evaluation w x) a).symm

lemma preserves_range (w : Labels) (f : OriginalAlgebra) :
    functionDeck w f.val ∈ evaluation.range := by
  obtain ⟨a,ha⟩ := f.property
  refine ⟨FourRootCoordinateRingSigns318.finiteEnd
    PELOriginalCommonContactBase318.branches (OriginalContactInertiaBasis318.basis w) a,?_⟩
  exact (evaluation_deck w a).trans (congrArg (functionDeck w) ha)

/-- An actual automorphism of the literal original-function algebra. -/
@[expose] def deck (w : Labels) : OriginalAlgebra ≃ₐ[ℂ] OriginalAlgebra where
  toFun f := ⟨functionDeck w f.val,preserves_range w f⟩
  invFun f := ⟨(functionDeck w).symm f.val,by
    change functionDeck w⁻¹ f.val ∈ evaluation.range
    exact preserves_range w⁻¹ f⟩
  left_inv f := Subtype.ext ((functionDeck w).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((functionDeck w).apply_symm_apply f.val)
  map_mul' f g := Subtype.ext ((functionDeck w).map_mul f.val g.val)
  map_add' f g := Subtype.ext ((functionDeck w).map_add f.val g.val)
  commutes' c := Subtype.ext ((functionDeck w).commutes c)

@[expose] def value (x : OriginalRegular) : OriginalAlgebra →ₐ[ℂ] ℂ where
  toFun f := f.val x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

lemma value_deck (w : Labels) (x : OriginalRegular) :
    (value x).comp (deck w).toAlgHom = value (originalAction w x) := rfl

/-- A genuine affine complex scheme attached to the ORIGINAL function
algebra, not a whole-curve or rational algebraization assertion. -/
abbrev affine : Scheme := Spec (CommRingCat.of OriginalAlgebra)
@[expose] def point (x : OriginalRegular) : Spec (CommRingCat.of ℂ) ⟶ affine :=
  Spec.map (CommRingCat.ofHom (value x).toRingHom)
@[expose] def schemeDeck (w : Labels) : affine ⟶ affine :=
  Spec.map (CommRingCat.ofHom (deck w).toRingHom)

/-- The genuine Spec map has the correct contravariant direction and
acts on every original regular point by its SAME original deck label. -/
theorem point_deck (w : Labels) (x : OriginalRegular) :
    point x ≫ schemeDeck w = point (originalAction w x) := by
  unfold point schemeDeck
  rw [←Spec.map_comp]
  rfl

/-- Original points are still separated by this literal range algebra.
This is not the missing assertion that every algebra element is a distinct
formal root polynomial or that all original meromorphic functions occur. -/
theorem values_separate (x y : OriginalRegular)
    (h : value x = value y) : x = y := by
  apply separates x y
  intro a
  exact AlgHom.congr_fun h ⟨evaluation a,⟨a,rfl⟩⟩
end PELOriginalCoordinateRangeDeck318
