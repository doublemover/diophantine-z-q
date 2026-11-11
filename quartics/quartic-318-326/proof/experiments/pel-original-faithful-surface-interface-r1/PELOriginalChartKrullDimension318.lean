module
public import IntegralFaithfulKrullDimension318
public import PELOriginalTwoDimensionalNormalization318
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public section
noncomputable section
namespace PELOriginalChartKrullDimension318
open AlgebraicGeometry CategoryTheory
open PELOriginalCandidateAffineCharts318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0<τ.im) (j : Label 3)
/-- Native ring Krull dimension TWO for every ENTIRE original chart.
The proof consumes a whole finite faithful polynomial normalization. -/
lemma dimension : ringKrullDim (CoordinateChart τ hτ j)=2 := by
  obtain ⟨g,hg,hf⟩ :=
    PELOriginalTwoDimensionalNormalization318.exists_two_variable_normalization τ hτ j
  let R := MvPolynomial (Fin 2) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : Module.Finite R A := hf
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : Algebra.IsIntegral R A := ⟨fun x => IsIntegral.of_finite R x⟩
  calc
    ringKrullDim A=ringKrullDim R := IntegralFaithfulKrullDimension318.dimension R A
    _=2 := by simp [R]
/-- The literal whole affine scheme chart has native topological
Krull dimension two, including all nonclosed points. -/
lemma spec_dimension :
    topologicalKrullDim (Spec (CommRingCat.of (CoordinateChart τ hτ j)))=2 := by
  change topologicalKrullDim (PrimeSpectrum (CoordinateChart τ hτ j))=2
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact dimension τ hτ j
end PELOriginalChartKrullDimension318
