module
public import IntegralOriginalZeroKernel318
public import ContactOriginalZeroKernelIso318
public import ContactUniversalZeroSpecialization318
public import ContactUniversalNonzeroLocus318
public import ContactFieldIntegralLine318
public section
noncomputable section
namespace ContactUniversalNonzeroFiberIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318 ContactUniversalZeroSpecialization318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K]
  (g : parameterRing R c L →ₐ[ℚ] K)
local instance : Algebra R K := (g.comp (parameterCoefficient R c L)).toAlgebra
local notation "N" => classifiedLine R c L K g
local notation "t" => classifiedSection R c L hz K g
local notation "p" => ContactGlobalSectionZero318.into K c N t
variable (hg : ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) K
  (parameterPoint R c L K g)∈ContactUniversalNonzeroLocus318.locus R c L hz)

/-- EVERY field point of the explicit nonzero parameter open has an
actual invertible zero-ideal module for the SAME classified section.
Integrality is supplied for the exact original field curve, and nonzero
is supplied by the actual parameter-open membership. -/
@[expose] def iso : (FramedLineInverse318.inverse N).object ≅ ActualClosedIdealModule318.object p :=
  IntegralOriginalZeroKernel318.iso N t
    ((ContactUniversalNonzeroLocus318.classified_nonzero_iff R c L hz K g).mp hg)
    (ContactOriginalZeroKernelIso318.rings K c) (ContactOriginalZeroKernelIso318.charts K c)
    (ContactOriginalZeroKernelIso318.cover K c) p
    (ContactOriginalZeroKernelIso318.zeroCharts K c N t)
    (ContactOriginalZeroKernelIso318.zero_squares K c N t)

@[reassoc] lemma iso_inclusion : (iso R c L hz K g hg).hom ≫
    ActualClosedIdealModule318.inclusion p=InverseLineSectionContraction318.hom N t :=
  IntegralOriginalZeroKernel318.iso_inclusion N t
    ((ContactUniversalNonzeroLocus318.classified_nonzero_iff R c L hz K g).mp hg)
    (ContactOriginalZeroKernelIso318.rings K c) (ContactOriginalZeroKernelIso318.charts K c)
    (ContactOriginalZeroKernelIso318.cover K c) p
    (ContactOriginalZeroKernelIso318.zeroCharts K c N t)
    (ContactOriginalZeroKernelIso318.zero_squares K c N t)

/-- This is the SAME geometric specialization of the original universal
zero closed subscheme, not an independently chosen fiber divisor. -/
@[expose] def zeroBaseChange := ContactUniversalZeroSpecialization318.iso R c L hz K g

@[reassoc] lemma zeroBaseChange_into : (zeroBaseChange R c L hz K g).hom ≫
    pullback.fst _ _=p := ContactUniversalZeroSpecialization318.iso_fst R c L hz K g
end ContactUniversalNonzeroFiberIdeal318
