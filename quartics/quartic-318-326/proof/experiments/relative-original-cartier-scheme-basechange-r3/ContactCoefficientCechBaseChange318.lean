module
public import ContactCoefficientNativeSections318
public import TwoChartCokernelBaseChange318
public section
noncomputable section
namespace ContactCoefficientCechBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open ContactCoefficientNativeSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _

/-- The actual coefficient-linear finite restriction square, now on all
tensors, follows from the geometric square on every old section. -/
lemma finite_square : (overlapEquivalence R S f c L).toLinearMap.comp
    ((ContactOriginalRelativeOverlapSpan318.finiteMap R c L).baseChange S) =
  (ContactOriginalRelativeOverlapSpan318.finiteMap S c (L' R S f c L)).comp
    (finiteEquivalence R S f c L).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s x
  simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul]
  rw [overlap_pure,finite_pure,LinearMap.map_smul]
  exact congrArg (fun y => s • y) (ContactCoefficientRestrictionSquares318.finite R S f c L x)

lemma infinity_square : (overlapEquivalence R S f c L).toLinearMap.comp
    ((ContactOriginalRelativeOverlapSpan318.infinityMap R c L).baseChange S) =
  (ContactOriginalRelativeOverlapSpan318.infinityMap S c (L' R S f c L)).comp
    (infinityEquivalence R S f c L).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s x
  simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul]
  rw [overlap_pure,infinity_pure,LinearMap.map_smul]
  exact congrArg (fun y => s • y) (ContactCoefficientRestrictionSquares318.infinity R S f c L x)

/-- Base change of the LITERAL original Cech quotient for every original
line and every coefficient map. All three comparisons and both original
restriction squares are constructed above; none is a caller premise. -/
@[expose] def equivalence :
    S ⊗[R] (originalSections R c L ⧸ ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L) ≃ₗ[S]
      originalSections S c (L' R S f c L) ⧸
        ContactRelativeOriginalDerivedQuotient318.imageBoundary S c (L' R S f c L) :=
  TwoChartCokernelBaseChange318.equivalence S
    (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L)
    (ContactOriginalRelativeOverlapSpan318.finiteMap S c (L' R S f c L))
    (ContactOriginalRelativeOverlapSpan318.infinityMap S c (L' R S f c L))
    (finiteEquivalence R S f c L) (infinityEquivalence R S f c L)
    (overlapEquivalence R S f c L) (finite_square R S f c L) (infinity_square R S f c L)

lemma pure_tensor (s : S) (x : originalSections R c L) :
    equivalence R S f c L
      (s ⊗ₜ[R] (ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ x) =
    (ContactRelativeOriginalDerivedQuotient318.imageBoundary S c (L' R S f c L)).mkQ
      (overlapEquivalence R S f c L (s ⊗ₜ[R] x)) :=
  TwoChartCokernelBaseChange318.equivalence_tmul _ _ _ _ _ _ _ _ _ _ s x
end ContactCoefficientCechBaseChange318
