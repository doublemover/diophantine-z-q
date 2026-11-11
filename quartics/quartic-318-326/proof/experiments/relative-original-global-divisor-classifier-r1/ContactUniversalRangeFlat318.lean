module
public import ContactUniversalResidueNonzero318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactUniversalRangeFlat318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : A →ₐ[ℚ] T)
local instance : Algebra A T := g.toAlgebra
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "a" => Spec.map (CommRingCat.ofHom g.toRingHom)

/-- Actual image containment in the nonzero parameter open implies the
literal maximal-residue point condition. No density or closed-point
sufficiency assertion is used; each residue point is simply mapped. -/
lemma maximal_points (hg : ∀ t : Spec T, a t∈W) :
    ContactUniversalResidueNonzero318.MaximalPointsInLocus R c L hz T g := by
  intro m hm
  letI := hm
  let x : PrimeSpectrum T := PrimeSpectrum.comap (Ideal.Quotient.mk m) ⟨⊥,inferInstance⟩
  exact hg x

/-- Flatness of the SAME globally glued zero scheme over every affine
coefficient test whose image is in the actual nonzero parameter open.
The two original quotient charts now glue as a genuine open cover. -/
theorem global_flat (hg : ∀ t : Spec T, a t∈W) :
    Flat (ContactGlobalResidueFlat318.projection T c
      (ContactUniversalResidueNonzero318.line R c L T g)
      (ContactUniversalResidueNonzero318.section R c L hz T g)) :=
  ContactGlobalResidueFlat318.flat T c _ _
    (ContactUniversalResidueNonzero318.residue_nonzero R c L hz T g
      (maximal_points R c L hz T g hg))
end ContactUniversalRangeFlat318
