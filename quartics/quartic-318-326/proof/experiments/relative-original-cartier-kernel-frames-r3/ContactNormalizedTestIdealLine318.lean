module
public import ContactNormalizedCartierTest318
public import ContactResidueActualIdealLine318
public import ContactUniversalRangeCartier318
public import ContactNormalizedGlobalClosedFamily318
public import RestrictedFamilyOriginal318
public import ContactUniversalClassifiedZeroParameter318
public import ContactNormalizedChartZeroFamily318
public section
noncomputable section
namespace ContactNormalizedTestIdealLine318
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
local notation "S" => ContactNormalizedCartierTest318.ring R c L hz i
local notation "g" => ContactNormalizedCartierTest318.coefficient R c L hz i
local notation "N" => ContactNormalizedCartierTest318.line R c L hz i
local notation "s" => ContactNormalizedCartierTest318.section R c L hz i
local notation "p" => ContactNormalizedCartierTest318.into R c L hz i
lemma residue_nonzero : ContactResidueRegularFlat318.ResidueNonzero S c N s :=
  ContactUniversalResidueNonzero318.residue_nonzero R c L hz S g
    (ContactUniversalRangeFlat318.maximal_points R c L hz S g
      (ContactNormalizedCartierTest318.image_nonzero R c L hz i))

/-- On every literal normalized coefficient chart, the ACTUAL zero ideal
is the inverse of the SAME original pulled line, with no residual
regularity/nonzero/kernel premise and with its inclusion fixed. -/
@[expose] def iso : (FramedLineInverse318.inverse N).object ≅ ActualClosedIdealModule318.object p :=
  ContactResidueActualIdealLine318.iso S c N s (residue_nonzero R c L hz i)
@[reassoc] lemma iso_inclusion : (iso R c L hz i).hom ≫ ActualClosedIdealModule318.inclusion p=
    InverseLineSectionContraction318.hom N s :=
  ContactResidueActualIdealLine318.iso_inclusion S c N s (residue_nonzero R c L hz i)

@[expose] def line : Line (curve S c) :=
  ContactResidueActualIdealLine318.line S c N s (residue_nonzero R c L hz i)
lemma line_object : (line R c L hz i).object=ActualClosedIdealModule318.object p := rfl
lemma original_inverse_class : classOf (line R c L hz i)=classOf (FramedLineInverse318.inverse N) :=
  LineSheafClass318.classOf_eq (iso R c L hz i).symm
end ContactNormalizedTestIdealLine318
