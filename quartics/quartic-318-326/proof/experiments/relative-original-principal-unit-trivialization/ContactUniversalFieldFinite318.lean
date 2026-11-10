module
public import ContactUniversalRangeFlat318
public import ContactFieldGlobalZeroFinite318
public section
noncomputable section
namespace ContactUniversalFieldFinite318
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
variable (T : CommRingCat.{0}) [Field T] [Algebra ℚ T] (g : A →ₐ[ℚ] T)
local instance : Algebra A T := g.toAlgebra
local instance : Algebra R T := (g.comp (parameterCoefficient R c L)).toAlgebra
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "a" => Spec.map (CommRingCat.ofHom g.toRingHom)

/-- The actual pulled universal global section is nonzero for a field
test lying in the existing nonzero parameter open. The original composition
map detects this without silently replacing the pulled section. -/
lemma section_ne_zero (hg : ∀ t : Spec T, a t∈W) :
    ContactUniversalResidueNonzero318.section R c L hz T g≠0 := by
  have hm : ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) T
      (parameterPoint R c L T g)∈W := hg ⟨⊥,inferInstance⟩
  have hn := (ContactUniversalNonzeroLocus318.geometric_nonzero_iff R c L hz T g).mp hm
  intro hs
  exact hn (by rw [show OriginalSectionPullbackComposition318.pull
    (ContactRelativeCoefficientChange318.curveMap A T g c) (universalLine R c L).object
    (universalSection R c L hz)=0 from hs,map_zero])

/-- A finite morphism for the SAME original globally pulled universal
zero over each actual field test in the nonzero parameter open. -/
theorem finite (hg : ∀ t : Spec T, a t∈W) :
    IsFinite (ContactGlobalResidueFlat318.projection T c
      (ContactUniversalResidueNonzero318.line R c L T g)
      (ContactUniversalResidueNonzero318.section R c L hz T g)) :=
  ContactFieldGlobalZeroFinite318.finite T c _ _ (section_ne_zero R c L hz T g hg)
end ContactUniversalFieldFinite318
