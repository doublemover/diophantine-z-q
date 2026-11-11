module
public import ContactNormalizedZeroIntersection318
public section
noncomputable section
namespace ContactLiteralTripleZeroFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i j k : Fin F.size)
abbrev ring := CommRingCat.of (ProjectiveParameterSliceTripleAlgebra318.algebra R P i j k)
local notation "S" => ring R c L hz i j k
instance rationalAlgebra : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
instance rationalTower : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
@[expose] def coefficient : R →ₐ[ℚ] S := IsScalarTower.toAlgHom ℚ R S
local notation "f" => coefficient R c L hz i j k
local notation "a" => ProjectiveParameterSliceTripleAlgebra318.universal R P i j k
local notation "q" => ProjectiveParameterSliceTriplePullback318.first R P i j k
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "zinc" => ContactNormalizedZeroTransitions318.inclusion R c L hz

/-- The arbitrary-test normalized classifier specializes to EXACTLY the
original iterated-localization triple leg, not an unspecified isomorphic
parameter arrow. Equality is checked on all original quotient elements. -/
lemma testMap_eq : ContactNormalizedPointZeroFamily318.testMap R c L hz S f i a.point a.first_eq=
    q ≫ inc i j := by
  rw [ContactNormalizedPointZeroFamily318.testMap,
    ProjectiveParameterSliceTriplePullback318.first,
    ProjectiveParameterSliceSchemes318.inclusion,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ContactNormalizedPointZeroFamily318.sliceMap_mk R c L hz S f i a.point a.first_eq z

/-- The ORIGINAL geometric triple intersection is identified with the
original chart-family triple on its literal coefficient algebra. Hence
the already constructed scheme-level normalization cycle has the exact
geometric domain required for gluing, not just test-point information. -/
@[expose] def intersectionIso : pullback (zinc i j) (zinc i k) ≅
    ContactNormalizedTripleFamilies318.family R c L hz S f a :=
  ContactNormalizedZeroIntersection318.iso R c L hz i j k ≪≫
    pullback.congrHom rfl (testMap_eq R c L hz i j k).symm

/-- The actual three normalized family comparisons satisfy the cyclic
identity on the literal triple algebra, including all nilpotents. -/
lemma literal_cycle :
    (ContactNormalizedTripleFamilies318.rotation R c L hz S f
      (ProjectiveParameterSliceTriplePoints318.rotate R P S j k i
        (ProjectiveParameterSliceTriplePoints318.rotate R P S i j k a))).hom ≫
    (ContactNormalizedTripleFamilies318.rotation R c L hz S f
      (ProjectiveParameterSliceTriplePoints318.rotate R P S i j k a)).hom ≫
    (ContactNormalizedTripleFamilies318.rotation R c L hz S f a).hom=
    eqToHom (congrArg (ContactNormalizedTripleFamilies318.family R c L hz S f)
      (ProjectiveParameterSliceTriplePoints318.rotate_three R P S i j k a)) :=
  ContactNormalizedTripleFamilies318.cycle R c L hz S f a
end ContactLiteralTripleZeroFamily318
