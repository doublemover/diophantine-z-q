module
public import ContactRelativeFiniteProjectiveHZero318
public import ContactRelativeTwistedCoordinates318
public import TwoChartJetDifferential318
public section
noncomputable section
namespace ContactRelativeTwistKernel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeWholeOpenSections318
open ContactRelativeCoefficientWholeSections318 ContactRelativeGeometricTwist318
open OriginalCoefficientCohomology318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)
local instance (N : Line (curve R c)) : Module R (finiteSections R c N) := finiteModule R c N
local instance (N : Line (curve R c)) : Module R (infinitySections R c N) := infinityModule R c N
local instance (N : Line (curve R c)) : Module R (originalSections R c N) := overlapModule R c N
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
local instance (N : Line (curve R c)) (U : (curve R c).Opens) : Module R Γ(N.object,U) :=
  sectionModule R (ContactRelativeStructuralHOne318.projection R c) N U

/-- The actual full-open untwisting is coefficient-linear because its
original section-ring linearity respects the independently structural R map. -/
@[expose] def finiteAmbient (U : (curve R c).Opens) (hU : U ≤ finiteOpen R c) :
    Γ((twist R c L d).object,U) ≃ₗ[R] Γ(L.object,U) where
  __ := (ContactRelativeTwistedCoordinates318.finiteCoordinates R c L d U hU).toAddEquiv
  map_smul' r x :=
    (ContactRelativeTwistedCoordinates318.finiteCoordinates R c L d U hU).map_smul
      (scalar R (ContactRelativeStructuralHOne318.projection R c) U r) x

@[expose] def infinityAmbient (U : (curve R c).Opens) (hU : U ≤ infinityOpen R c) :
    Γ((twist R c L d).object,U) ≃ₗ[R] Γ(L.object,U) where
  __ := (ContactRelativeTwistedCoordinates318.infinityCoordinates R c L d U hU).toAddEquiv
  map_smul' r x :=
    (ContactRelativeTwistedCoordinates318.infinityCoordinates R c L d U hU).map_smul
      (scalar R (ContactRelativeStructuralHOne318.projection R c) U r) x

@[expose] def finiteCoordinates : finiteSections R c (twist R c L d) ≃ₗ[R] finiteSections R c L :=
  (finiteEquivalence R c (twist R c L d)).trans
    ((finiteAmbient R c L d _ le_rfl).trans (finiteEquivalence R c L).symm)
@[expose] def infinityCoordinates : infinitySections R c (twist R c L d) ≃ₗ[R] infinitySections R c L :=
  (infinityEquivalence R c (twist R c L d)).trans
    ((infinityAmbient R c L d _ le_rfl).trans (infinityEquivalence R c L).symm)
@[expose] def overlapCoordinates : originalSections R c (twist R c L d) ≃ₗ[R] originalSections R c L :=
  (overlapEquivalence R c (twist R c L d)).trans
    ((finiteAmbient R c L d _ inf_le_left).trans (overlapEquivalence R c L).symm)

@[expose] def shift : originalSections R c L ≃ₗ[R] originalSections R c L where
  toFun := RelativeLaurentScalar318.shift R (originalSections R c L) d
  invFun := RelativeLaurentScalar318.shift R (originalSections R c L) (-d)
  left_inv x := by
    change (LaurentPolynomial.T (-d) : LaurentPolynomial R) • ((LaurentPolynomial.T d : LaurentPolynomial R) • x)=x
    rw [smul_smul,← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero,one_smul]
  right_inv x := by
    change (LaurentPolynomial.T d : LaurentPolynomial R) • ((LaurentPolynomial.T (-d) : LaurentPolynomial R) • x)=x
    rw [smul_smul,← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,one_smul]
  map_add' := map_add _
  map_smul' := map_smul _

@[expose] def positiveDifference := TwoChartJetDifferential318.positiveDifference
  (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
  (ContactOriginalRelativeOverlapSpan318.infinityMap R c L) (shift R c L d)

lemma square : (positiveDifference R c L d).comp
    ((finiteCoordinates R c L d).prodCongr (infinityCoordinates R c L d)).toLinearMap =
    (overlapCoordinates R c L d).toLinearMap.comp
      (ContactRelativeCechProjective318.difference R c (twist R c L d)) := by
  ext x
  change _ = ContactRelativeTwistedCoordinates318.coordinates R c L d
    (overlapEquiv R c (twist R c L d)
      (finiteRestriction R c (twist R c L d) x.1-infinityRestriction R c (twist R c L d) x.2))
  rw [map_sub,ContactRelativeWholeOpenSections318.finite_square,
    ContactRelativeWholeOpenSections318.infinity_square,map_sub,
    ContactRelativeTwistedCoordinates318.finite_restriction,
    ContactRelativeTwistedCoordinates318.infinity_restriction]
  rfl

/-- The positive kernel is identified with the ACTUAL global sections of
the original geometric twist, through its genuine full-chart frames. -/
@[expose] def globalEquivalence : Γ((twist R c L d).object,⊤) ≃ₗ[R]
    LinearMap.ker (positiveDifference R c L d) :=
  (ContactRelativeOriginalHZero318.equivalence R c (twist R c L d)).trans
    (KernelComparisonTransport318.equivalence
      (ContactRelativeCechProjective318.difference R c (twist R c L d))
      (positiveDifference R c L d)
      ((finiteCoordinates R c L d).prodCongr (infinityCoordinates R c L d))
      (overlapCoordinates R c L d) (square R c L d))

theorem finite_projective
    (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L d),x=0) :
    Module.Finite R (LinearMap.ker (positiveDifference R c L d)) ∧
    Module.Projective R (LinearMap.ker (positiveDifference R c L d)) := by
  letI := (ContactRelativeFiniteProjectiveHZero318.finite_projective R c (twist R c L d) hz).1
  letI := (ContactRelativeFiniteProjectiveHZero318.finite_projective R c (twist R c L d) hz).2
  exact ⟨Module.Finite.equiv (globalEquivalence R c L d),
    Module.Projective.of_equiv (globalEquivalence R c L d)⟩

lemma surjective (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L d),x=0) :
    Function.Surjective (positiveDifference R c L d) := by
  intro x
  obtain ⟨y,hy⟩ := ContactRelativeCechProjective318.surjective_of_h1_zero R c (twist R c L d) hz
    ((overlapCoordinates R c L d).symm x)
  refine ⟨((finiteCoordinates R c L d).prodCongr (infinityCoordinates R c L d)) y,?_⟩
  have h := LinearMap.congr_fun (square R c L d) y
  change positiveDifference R c L d _ = overlapCoordinates R c L d
    (ContactRelativeCechProjective318.difference R c (twist R c L d) y) at h
  rw [hy,LinearEquiv.apply_symm_apply] at h
  exact h
end ContactRelativeTwistKernel318
