module
public import ProjectiveKernelNormalizationAmbient318
public import ContactOriginalNormalizedKernelCharts318
public section
noncomputable section
namespace ContactOriginalNormalizedKernelScheme318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318 ContactOriginalSectionKernel318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2
local notation "P" => zeroTerm R c L
local notation "Q" => oneTerm R c L
local notation "d" => boundary R c L
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
/-- ACTUAL global normalized-kernel scheme for every original line,
closed in the normalized finite-projective TERM parameter, not projective H0. -/
abbrev scheme : Scheme := ProjectiveKernelNormalizedGluing318.scheme R P Q d
abbrev projection : scheme R c L ⟶ Spec R := ProjectiveKernelNormalizedGluing318.projection R P Q d
abbrev closedInto : scheme R c L ⟶ ProjectiveParameterSliceGluing318.scheme R P :=
  ProjectiveKernelNormalizedGluing318.closedInto R P Q d
instance closed : IsClosedImmersion (closedInto R c L) := inferInstance
abbrev cover : (scheme R c L).OpenCover := ProjectiveKernelNormalizedGluing318.cover R P Q d
abbrev chartInto (i : Fin F.size) : ContactOriginalNormalizedKernelCharts318.slice R c L i ⟶ scheme R c L :=
  ProjectiveKernelNormalizedGluing318.into R P Q d i
@[expose] def localNormalize (i : Fin F.size) :
    ContactOriginalNormalizedKernelCharts318.principal R c L i ⟶ scheme R c L :=
  ProjectiveKernelNormalizationAmbient318.localMap R P Q d i
lemma localNormalize_eq (i : Fin F.size) : localNormalize R c L i=
    ContactOriginalNormalizedKernelCharts318.normalize R c L i ≫ chartInto R c L i := rfl
/-- Exact map to the old normalized TERM parameter;the original kernel
principal chart inclusion and old scalar normalization are retained. -/
lemma localNormalize_ambient (i : Fin F.size) : localNormalize R c L i ≫ closedInto R c L=
    Spec.map (CommRingCat.ofHom
      (ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i).toRingHom) ≫
        ProjectiveParameterPrincipalNormalization318.map R P i :=
  ProjectiveKernelNormalizationAmbient318.localMap_ambient R P Q d i

end ContactOriginalNormalizedKernelScheme318
