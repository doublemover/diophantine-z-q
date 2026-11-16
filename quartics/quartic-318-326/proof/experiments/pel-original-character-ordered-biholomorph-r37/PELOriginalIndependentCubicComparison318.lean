module
public import OriginalPeriodIndependentBiholomorph318
public import PELOriginalAlgebraicDoubling318
public section
noncomputable section
namespace PELOriginalIndependentCubicComparison318
open PELOriginalInvolutionTower318 PELOriginalCharacterQuotient318
open PELOriginalInvolutionComplexAtlas318 PELOriginalUniformizationOnly318
open ComplexAffineFreeTranslation318 OriginalPeriodPlaneOverlap318
open OriginalPeriodCompletedPointIdentification318
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
variable (i : Fin 4) (L : AddSubgroup ℂ) [DiscreteTopology L]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i
local instance : ChartedSpace ℂ (CharacterBase i) := PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := PELOriginalCharacterComplexAtlas318.character_manifold i
variable (u : InvolutionBase i ≃ₜ Torus L)
local instance : CompactSpace (Torus L) := quotient_compact i L u
local instance : ChartedSpace ℂ (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.complex_manifold L
variable (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
  (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm)

/-- The actual involution curve maps to the independently topologized
and complex-charted projective period cubic. Original curve uniformization
u remains explicit; neither a PEL surface lattice nor a j-map replaces it. -/
@[expose] def involution : InvolutionBase i ≃ₜ CompletedPlane L :=
  u.trans (OriginalPeriodIndependentBiholomorph318.comparison L)

/-- The actual index-eight character quotient maps biholomorphically to
the SAME independent completed cubic, not an unspecified isogenous curve. -/
@[expose] def characterComparison : CharacterBase i ≃ₜ CompletedPlane L :=
  (character i L u hu huinv).trans (OriginalPeriodIndependentBiholomorph318.comparison L)

include hu huinv in
lemma involution_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (involution i L u) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (involution i L u).symm := by
  have h:=OriginalPeriodIndependentBiholomorph318.biholomorphic L
  exact ⟨h.1.comp hu,huinv.comp h.2⟩

lemma character_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterComparison i L u hu huinv) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterComparison i L u hu huinv).symm := by
  have hc:=original_uniformization_only i L u hu huinv
  have h:=OriginalPeriodIndependentBiholomorph318.biholomorphic L
  exact ⟨h.1.comp hc.1,hc.2.1.comp h.2⟩

/-- Actual curve maps retain the PREVIOUS native algebraic points and
actual all-scheme-point comparison, including their original infinity. -/
lemma involution_scheme (p : InvolutionBase i) :
    schemeEquivalence L (involution i L u p)=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence L
        (PELOriginalAlgebraicDoubling318.involutionPoints i L u p) := by
  change schemeEquivalence L (OriginalPeriodIndependentBiholomorph318.comparison L (u p))=_
  rw [OriginalPeriodIndependentBiholomorph318.actual_scheme]
  exact (OriginalPeriodCompletedSchemeBijection318.native_original L (u p)).symm

lemma character_scheme (p : CharacterBase i) :
    schemeEquivalence L (characterComparison i L u hu huinv p)=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence L
        (PELOriginalAlgebraicDoubling318.characterPoints i L u hu huinv p) := by
  change schemeEquivalence L (OriginalPeriodIndependentBiholomorph318.comparison L
    (character i L u hu huinv p))=_
  rw [OriginalPeriodIndependentBiholomorph318.actual_scheme]
  exact (OriginalPeriodCompletedSchemeBijection318.native_original L (character i L u hu huinv p)).symm

/-- The exact original residual four-cover, on these SAME actual complex
curves and their actual scheme-valued points, is native elliptic doubling.
No scheme-morphism algebraization or published rational coefficients are
inferred from this analytic/point-level identification. -/
theorem residual_native_doubling (p : InvolutionBase i) :
    schemeEquivalence L (characterComparison i L u hu huinv (toCharacterBase i p))=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence L
        (PELOriginalAlgebraicDoubling318.involutionPoints i L u p+
          PELOriginalAlgebraicDoubling318.involutionPoints i L u p) := by
  rw [character_scheme,PELOriginalAlgebraicDoubling318.original_algebraic_doubling]
end PELOriginalIndependentCubicComparison318
