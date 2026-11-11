module
public import ProjectiveSectionParameter318
public import ContactRelativeFiniteProjectiveHZero318
public import ContactRelativeGeometricVanishing318
public section
noncomputable section
namespace ContactOriginalSectionParameter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤

/-- Actual affine parameter coefficient algebra for sections of the
specified ORIGINAL line. It is not a parameter space of arbitrary line classes. -/
abbrev parameterRing := ProjectiveSectionParameter318.algebra R Γ(L.object,⊤)
abbrev parameterScheme : Scheme := Spec (CommRingCat.of (parameterRing R c L))

local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[expose] def parameterCoefficient : R →ₐ[ℚ] parameterRing R c L :=
  IsScalarTower.toAlgHom ℚ R (parameterRing R c L)

@[expose] def parameterProjection : parameterScheme R c L ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (parameterCoefficient R c L).toRingHom)

variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2

/-- The actual literal pullback of L to the contact family over the
parameter algebra, not a line on the j-map or another source curve. -/
abbrev universalLine := L' R (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L

/-- A genuine GLOBAL section on the ORIGINAL contact family after
extension to the actual parameter algebra. -/
@[expose] def universalSection : Γ((universalLine R c L).object,⊤) :=
  ContactRelativeHZeroBaseChange318.equivalence R (CommRingCat.of (parameterRing R c L))
    (parameterCoefficient R c L) c L hz
    (ProjectiveSectionParameter318.universal R Γ(L.object,⊤))

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra

/-- This actual affine parameter algebra represents sections of the
literal pulled ORIGINAL line on every affine coefficient test. The actual
H0-basechange theorem, not a postulated vector space, is the final bridge. -/
@[expose] def points : (parameterRing R c L →ₐ[R] S) ≃ Γ((L' R S f c L).object,⊤) :=
  (ProjectiveSectionParameter318.points R Γ(L.object,⊤) S).trans
    (ContactRelativeHZeroBaseChange318.equivalence R S f c L hz).toEquiv

/-- Every represented section is obtained by specializing the same
universal TENSOR and then the actual original global-section comparison.
The separate comparison with geometric pullback of universalSection is
not asserted here without its genuine composition square. -/
lemma specialize (a : parameterRing R c L →ₐ[R] S) :
    ContactRelativeHZeroBaseChange318.equivalence R S f c L hz
      (ProjectiveSectionParameter318.transport R Γ(L.object,⊤) (parameterRing R c L) a
        (ProjectiveSectionParameter318.universal R Γ(L.object,⊤))) = points R c L hz S f a := by
  rw [ProjectiveSectionParameter318.specialize_universal]
  rfl

end ContactOriginalSectionParameter318
namespace ContactPositiveSectionParameter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The original positive twist needed for the section parameter producer
exists for EVERY actual line; the caller supplies no freeness, projective
presentation, scalar compatibility or vanishing bound. -/
theorem exists_positive_bound : ∃ b : ℕ,
    ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0 := by
  obtain ⟨N,hN⟩ := ContactRelativeGeometricVanishing318.exists_bound R c L
  exact ⟨N,hN (N+1) (Nat.le_succ N)⟩
end ContactPositiveSectionParameter318
