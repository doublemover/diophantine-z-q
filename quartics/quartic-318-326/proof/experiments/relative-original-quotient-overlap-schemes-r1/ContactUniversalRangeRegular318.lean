module
public import ContactUniversalRangeFlat318
public import ContactResidueSectionRegular318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactUniversalRangeRegular318
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

/-- Genuine intrinsic regularity on BOTH complete original affine
charts over every actual coefficient test in the nonzero parameter
open. This is over the entire test ring, including nilpotents, not just
its residue fields. All residue nonvanishing inputs are constructed. -/
theorem chart_regularity (hg : ∀ t : Spec T, a t∈W) :
    SectionZeroRegularCoordinate318.Regular (T ⊗[ℚ] finiteRing c)
      (OriginalLineAffineModel318.sections (CommRingCat.of (T ⊗[ℚ] finiteRing c))
        (LineSheafPullback318.line (finiteInto T c) N)) (pull (finiteInto T c) N.object s) ∧
    SectionZeroRegularCoordinate318.Regular (T ⊗[ℚ] infinityRing c)
      (OriginalLineAffineModel318.sections (CommRingCat.of (T ⊗[ℚ] infinityRing c))
        (LineSheafPullback318.line (infinityInto T c) N)) (pull (infinityInto T c) N.object s) := by
  have hn := ContactUniversalResidueNonzero318.residue_nonzero R c L hz T g
    (ContactUniversalRangeFlat318.maximal_points R c L hz T g hg)
  exact ⟨ContactResidueSectionRegular318.finite_regular T c N s hn,
    ContactResidueSectionRegular318.infinity_regular T c N s hn⟩
end ContactUniversalRangeRegular318
