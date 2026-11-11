module
public import ContactRelativeTwistKernel318
public section
noncomputable section
namespace ContactTwistGlobalCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (d : ℤ)
local instance (N : Line (curve R c)) : Module R (finiteSections R c N) := finiteModule R c N
local instance (N : Line (curve R c)) : Module R (infinitySections R c N) := infinityModule R c N
local instance : Module R Γ((twist R c L d).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R
    (ContactRelativeStructuralHOne318.projection R c) (twist R c L d) ⊤

/-- Actual global restriction, followed by the original whole-chart
untwisting frame, with no change to the source contact curve. -/
@[expose] def finiteValue : Γ((twist R c L d).object,⊤) →ₗ[R] finiteSections R c L :=
  (ContactRelativeTwistKernel318.finiteCoordinates R c L d).toLinearMap.comp
    ((LinearMap.fst R _ _).comp
      (ContactRelativeOriginalHZero318.pair R c (twist R c L d)))
@[expose] def infinityValue : Γ((twist R c L d).object,⊤) →ₗ[R] infinitySections R c L :=
  (ContactRelativeTwistKernel318.infinityCoordinates R c L d).toLinearMap.comp
    ((LinearMap.snd R _ _).comp
      (ContactRelativeOriginalHZero318.pair R c (twist R c L d)))

lemma coordinates (s : Γ((twist R c L d).object,⊤)) :
    (ContactRelativeTwistKernel318.globalEquivalence R c L d s).val =
      (finiteValue R c L d s,infinityValue R c L d s) := rfl

/-- Every compatible original pair comes from the SAME genuine global
section of the positive twist, retaining both exact chart coordinates. -/
theorem exists_global (a : finiteSections R c L) (b : infinitySections R c L)
    (h : ContactOriginalRelativeOverlapSpan318.finiteMap R c L a =
      ContactRelativeTwistKernel318.shift R c L d
        (ContactOriginalRelativeOverlapSpan318.infinityMap R c L b)) :
    ∃ s : Γ((twist R c L d).object,⊤),
      finiteValue R c L d s = a ∧ infinityValue R c L d s = b := by
  let z : LinearMap.ker (ContactRelativeTwistKernel318.positiveDifference R c L d) :=
    ⟨(a,b),sub_eq_zero.mpr h⟩
  refine ⟨(ContactRelativeTwistKernel318.globalEquivalence R c L d).symm z,?_⟩
  have hz := congrArg Subtype.val
    ((ContactRelativeTwistKernel318.globalEquivalence R c L d).apply_symm_apply z)
  rw [coordinates] at hz
  exact ⟨congrArg Prod.fst hz,congrArg Prod.snd hz⟩
end ContactTwistGlobalCoordinates318
