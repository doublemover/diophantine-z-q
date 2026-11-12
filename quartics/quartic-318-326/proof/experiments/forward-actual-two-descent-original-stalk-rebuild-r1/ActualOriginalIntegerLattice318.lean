module
public import ActualOriginalUnitLocalSeries318
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace ActualOriginalIntegerLattice318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318
set_option maxHeartbeats 16000000

/-- The linear image of precisely the original integer coordinate map.
No coordinate or ambient norm change is introduced. -/
@[expose] def integerEmbedLinear : Coordinates ℤ →ₗ[ℤ] Coordinates ℝ where
  toFun := integerEmbed
  map_add' := integerEmbed_add
  map_smul' n x := by simp [integerEmbed,smul_eq_mul,zsmul_eq_mul]

@[expose] def originalIntegerLattice : Submodule ℤ (Coordinates ℝ) :=
  LinearMap.range integerEmbedLinear

@[expose] def integerLatticeEquiv : Coordinates ℤ ≃ₗ[ℤ] originalIntegerLattice :=
  LinearEquiv.ofInjective integerEmbedLinear actual_integer_embedding_closed.injective

lemma actual_integer_lattice_value (z : Coordinates ℤ) :
    (integerLatticeEquiv z : Coordinates ℝ) = integerEmbed z := rfl

/-- The actual closed coordinate embedding gives discreteness of its
image, rather than assuming the image is a lattice by notation. -/
instance originalIntegerLattice_discrete : DiscreteTopology originalIntegerLattice := by
  change DiscreteTopology (Set.range integerEmbed)
  exact actual_integer_embedding_closed.isEmbedding.toHomeomorph.discreteTopology

lemma actual_original_integer_rank : Module.finrank ℤ originalIntegerLattice = 5 := by
  rw [←integerLatticeEquiv.finrank_eq]
  norm_num [Coordinates,Module.finrank_prod]

/-- A genuine five-dimensional lattice p-series in the original
product norm. The zero lattice vector contributes zero to this inverse
power, so Fourier estimates must handle it separately. -/
theorem actual_integer_norm_inverse_six :
    Summable (fun z : Coordinates ℤ => ‖integerEmbed z‖⁻¹^6) := by
  have hs := ZLattice.summable_norm_pow_inv originalIntegerLattice 6
    (by rw [actual_original_integer_rank]; norm_num)
  have ht := hs.comp_injective integerLatticeEquiv.injective
  change Summable (fun z : Coordinates ℤ => ‖integerEmbed z‖⁻¹^6) at ht
  exact ht

end ActualOriginalIntegerLattice318
