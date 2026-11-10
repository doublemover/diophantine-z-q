module
public import ContactUniversalRangeFlat318
public import ContactResidueCartierCharts318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactUniversalRangeCartier318
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

local notation "N" => ContactUniversalResidueNonzero318.line R c L T g
local notation "s" => ContactUniversalResidueNonzero318.section R c L hz T g

/-- Every original nonzero affine coefficient test carries the SAME
closed zero subscheme with actual Cartier charts. The image condition
produces residue nonvanishing and then full-ring regularity internally. -/
theorem regular_charts (hg : ∀ t : Spec T, a t∈W) :
    OriginalRegularClosedCharts318.Property (ContactGlobalSectionZero318.into T c N s) :=
  ContactResidueCartierCharts318.regular_charts T c N s
    (ContactUniversalResidueNonzero318.residue_nonzero R c L hz T g
      (ContactUniversalRangeFlat318.maximal_points R c L hz T g hg))
end ContactUniversalRangeCartier318
