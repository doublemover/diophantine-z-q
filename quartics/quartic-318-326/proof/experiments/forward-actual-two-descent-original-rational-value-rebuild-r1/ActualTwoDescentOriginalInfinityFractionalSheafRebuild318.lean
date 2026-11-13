module
public import ActualTwoDescentOriginalInfinityLocalPullbackRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityFractionalSheafRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentOriginalLocalFieldEmbeddingsRebuild318
universe u
variable {K : Type u} [Field K] [CharZero K]
local instance (n : K) : Algebra (InfinityLocalRing n) ((originalCubicScheme n).functionField) := (infinityEmbedding n).toAlgebra

def lattice (n : K) : Submodule (InfinityLocalRing n) ((originalCubicScheme n).functionField) :=
  ActualTwoDescentFractionalGeneratorModuleRebuild318.lattice (InfinityLocalRing n) ((originalCubicScheme n).functionField)
    (infinityEmbedding n (localU n))⁻¹

def moduleFrame (n : K) : InfinityLocalRing n ≃ₗ[InfinityLocalRing n] lattice n :=
  ActualTwoDescentFractionalGeneratorModuleRebuild318.frame (InfinityLocalRing n) ((originalCubicScheme n).functionField) _
    (inv_ne_zero (infinity_parameter_nonzero n)) (infinity_injective n)

/-- Full local fractional module is u inverse times the ACTUAL local
ring in the same original function field, not a pole-symbol token. -/
lemma mem_lattice (n : K) (z : (originalCubicScheme n).functionField) : z ∈ lattice n ↔
    ∃ r : InfinityLocalRing n,infinityEmbedding n r/(infinityEmbedding n (localU n))=z := by
  simp only [lattice,ActualTwoDescentFractionalGeneratorModuleRebuild318.mem_lattice,div_eq_mul_inv] <;> rfl

/-- The exact old infinity frame, followed by the explicit b/u map.
Global compatibility with the affine fractional embedding is separate. -/
def iso (n : K) (i : Fin 3) :
    (Scheme.Modules.pullback (ActualTwoDescentOriginalInfinityLocalPullbackRebuild318.map n)).obj
      (originalRootIdealSheaf n i) ≅
    tilde (R:=CommRingCat.of (InfinityLocalRing n)) (ModuleCat.of (InfinityLocalRing n) (lattice n)) :=
  ActualTwoDescentOriginalInfinityLocalPullbackRebuild318.frame n i ≪≫
  (tildeSelf (R:=CommRingCat.of (InfinityLocalRing n))).symm ≪≫
  (tilde.functor (CommRingCat.of (InfinityLocalRing n))).mapIso (moduleFrame n).toModuleIso

lemma module_value (n : K) (r : InfinityLocalRing n) : (moduleFrame n r : (originalCubicScheme n).functionField)=
    infinityEmbedding n r/(infinityEmbedding n (localU n)) := by
  change infinityEmbedding n r*(infinityEmbedding n (localU n))⁻¹=_
  rw [div_eq_mul_inv]
end ActualTwoDescentOriginalInfinityFractionalSheafRebuild318
