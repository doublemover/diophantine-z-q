module
public import ProjectiveLineIntegral318
public import OpenFunctionFieldSquare318
public section
noncomputable section
namespace ThreeJActualDominance318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJMonicAlgebra318 ThreeJLaurentEquiv318 ThreeJFiniteLaurentMap318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma baseMap_injective : Function.Injective ThreeJLaurentEquiv318.baseMap := by
  have hi : Function.Injective (algebraMap Base Model) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos monic (by
      rw [←Polynomial.natDegree_pos_iff_degree_pos,degree]
      decide)
  intro a b hab
  apply hi
  apply coordinateEquiv.injective
  simpa only [coordinate_base] using hab

instance affine_dominant : IsDominant finiteTargetMap := by
  constructor
  change DenseRange (PrimeSpectrum.comap ThreeJLaurentEquiv318.baseMap.toRingHom)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp baseMap_injective]
  exact bot_le

instance map_dominant : IsDominant ThreeProjectiveJMap318.map := by
  haveI : IsDominant (ProjectiveLineOverlap318.embedding ≫ ThreeProjectiveJMap318.map) := by
    rw [original_scheme_square]
    infer_instance
  exact IsDominant.of_comp ProjectiveLineOverlap318.embedding ThreeProjectiveJMap318.map

/-- The same global finite scheme map is surjective on every scheme point,
not merely on complex values or a selected generic chart. -/
theorem map_surjective : Surjective ThreeProjectiveJMap318.map := by
  letI := ThreeJGlobalFinite318.map_proper
  infer_instance

end ThreeJActualDominance318
