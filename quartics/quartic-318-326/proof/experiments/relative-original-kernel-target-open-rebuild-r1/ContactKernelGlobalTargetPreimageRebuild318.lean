module
public import ContactKernelGlobalTargetOpenRebuild318
public import ContactNowhereZeroNormalizationRebuild318
public section
noncomputable section
namespace ContactKernelGlobalTargetPreimageRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
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
local notation "S" => ContactOriginalGlobalKernelNormalizationRebuild318.source R c L
local notation "n" => ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
local notation "j" => ContactOriginalGlobalKernelNormalizationRebuild318.original R c L
local notation "V" => ContactKernelGlobalTargetOpenRebuild318.locus R c L
local notation "N" => ContactArbitraryNowhereZeroOpen318.locus R c L
include R c L in
/-- Equality of WHOLE source opens, proved on the actual full principal
cover. It is not merely equality on reduced or rational points. -/
lemma preimage : n ⁻¹ᵁ V=j ⁻¹ᵁ N := by
  ext x
  obtain ⟨i,y,rfl⟩ := (ProjectiveKernelNonzeroSourceRebuild318.cover R P Q d).exists_eq x
  have hn := congrArg (fun k => k y)
    (ProjectiveKernelGlobalNormalizationRebuild318.on_chart R P Q d i)
  have hj := congrArg (fun k => k y)
    (ProjectiveKernelNonzeroSourceRebuild318.chart_original R P Q d i)
  change (n (ProjectiveKernelNonzeroSourceRebuild318.chart R P Q d i y) ∈ V) ↔
    j (ProjectiveKernelNonzeroSourceRebuild318.chart R P Q d i y) ∈ N
  rw [hn,hj]
  change (ProjectiveKernelNormalizedLaurent318.projection R P Q d i y ∈
      ProjectiveKernelNormalizedGluing318.into R P Q d i ⁻¹ᵁ V) ↔
    y ∈ ContactKernelSliceOpenRebuild318.principalLocus R c L i
  rw [ContactKernelGlobalTargetOpenRebuild318.preimage]
  change (y ∈ ProjectiveKernelNormalizedLaurent318.projection R P Q d i ⁻¹ᵁ
    ContactKernelSliceOpenRebuild318.sliceLocus R c L i) ↔ _
  rw [←ContactKernelSliceOpenRebuild318.preimage]
end ContactKernelGlobalTargetPreimageRebuild318
