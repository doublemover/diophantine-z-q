module
public import ContactCoefficientAmbientUnit318
public import ContactDerivedCoefficientFunctor318
public section
noncomputable section
namespace ContactCanonicalHOneBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactOriginalDerivedCoefficientMap318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
local instance : Module S (NonreducedLineMayerVietoris318.H1 (pulled R S f c L)) :=
  OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c)
    (pulled R S f c L) 1

/-- The original tensor equivalence is the INDEPENDENT original derived
pullback on every original cohomology class, not merely an arbitrary
boundary-normalized quotient equivalence. -/
lemma on_original (x : NonreducedLineMayerVietoris318.H1 L) :
    ContactOriginalHOneBaseChange318.equivalence R S f c L (1 ⊗ₜ[R] x) = map R S f c L 1 x := by
  obtain ⟨s,rfl⟩ := ContactRelativeOriginalDerivedQuotient318.boundary_surjective R c L x
  rw [ContactOriginalHOneBaseChange318.representative,one_smul,
    ContactOriginalDerivedCoefficientMap318.representative]
  change NonreducedLineMayerVietoris318.boundary (pulled R S f c L)
    (finiteOpen S c) (infinityOpen S c) (cover S c)
    (overlapEquiv S c (pulled R S f c L)
      (ContactCoefficientLineCharts318.overlapRestriction R S f c L s)) = _
  rw [ContactCoefficientAmbientUnit318.square]

/-- Full scalar-extension normalization against the actual derived map. -/
lemma pure_tensor (s : S) (x : NonreducedLineMayerVietoris318.H1 L) :
    ContactOriginalHOneBaseChange318.equivalence R S f c L (s ⊗ₜ[R] x) =
      s • map R S f c L 1 x := by
  have hs : s • ((1 : S) ⊗ₜ[R] x) = s ⊗ₜ[R] x := by simp [smul_tmul']
  rw [← hs,map_smul,on_original]

/-- Universal uniqueness identifies the constructed isomorphism with
ANY S-linear realization of the original derived coefficient pullback.
This pins the canonical scalar extension, with no chosen cover or frame. -/
lemma unique (a : S ⊗[R] NonreducedLineMayerVietoris318.H1 L →ₗ[S]
    NonreducedLineMayerVietoris318.H1 (pulled R S f c L))
    (ha : ∀ x, a (1 ⊗ₜ[R] x) = map R S f c L 1 x) :
    a = (ContactOriginalHOneBaseChange318.equivalence R S f c L).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s x
  have hs : s • ((1 : S) ⊗ₜ[R] x) = s ⊗ₜ[R] x := by simp [smul_tmul']
  calc
    a (s ⊗ₜ[R] x) = s • a (1 ⊗ₜ[R] x) := by rw [← hs,map_smul]
    _ = s • map R S f c L 1 x := by rw [ha]
    _ = _ := (pure_tensor R S f c L s x).symm
end ContactCanonicalHOneBaseChange318
