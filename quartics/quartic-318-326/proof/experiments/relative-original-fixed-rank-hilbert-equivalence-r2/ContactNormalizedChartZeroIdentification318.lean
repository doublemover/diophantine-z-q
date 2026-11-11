module
public import RestrictedFamilyPullback318
public import ContactUniversalClassifiedZeroParameter318
public import ContactNormalizedChartZeroFamily318
public section
noncomputable section
namespace ContactNormalizedChartZeroIdentification318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (i : Fin F.size)
abbrev ring := CommRingCat.of (ProjectiveParameterSliceAlgebra318.algebra R Γ(L.object,⊤) i)
local notation "S" => ring R c L hz i
instance rationalAlgebra : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
instance rationalTower : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl

/-- Literal quotient of the ORIGINAL parameter algebra by x_i-1. -/
@[expose] def coefficient : A →ₐ[ℚ] S :=
  (Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R Γ(L.object,⊤) i)).restrictScalars ℚ
local notation "g" => coefficient R c L hz i
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "j" => ContactNormalizedChartZeroFamily318.parameterMap R c L hz i
lemma factor : j ≫ W.ι=Spec.map (CommRingCat.ofHom g.toRingHom) :=
  ProjectiveParameterSliceNonzero318.intoNonzero_fac R Γ(L.object,⊤) i

abbrev line := ContactUniversalZeroSpecialization318.classifiedLine R c L S g
abbrev section : Γ((line R c L hz i).object,⊤) :=
  ContactUniversalZeroSpecialization318.classifiedSection R c L hz S g

/-- The actual finite-flat family on this normalized chart is EXACTLY
the zero scheme of its classified section of the original pulled line.
Both the original coefficient/line associator and nested nonzero-open
restriction are consumed, preserving the actual parameter projection. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c (line R c L hz i) (section R c L hz i) ≅
    ContactNormalizedChartZeroFamily318.scheme R c L hz i :=
  ContactUniversalClassifiedZeroParameter318.iso R c L hz S g ≪≫
    (RestrictedFamilyPullback318.iso π W.ι j (Spec.map (CommRingCat.ofHom g.toRingHom))
      (factor R c L hz i)).symm
@[reassoc] lemma iso_projection : (iso R c L hz i).hom ≫
    ContactNormalizedChartZeroFamily318.projection R c L hz i=
    ContactGlobalResidueFlat318.projection S c (line R c L hz i) (section R c L hz i) := by
  rw [iso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    RestrictedFamilyPullback318.inv_projection,ContactUniversalClassifiedZeroParameter318.iso_projection]
end ContactNormalizedChartZeroIdentification318
