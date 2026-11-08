module
public import InfinityBranchUniqueness318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ActualInfinityEquation318
open PeriodEisenstein318 LatticeInvariants318 InfinityAnalyticChart318
open InfinityBranchUniqueness318
set_option maxHeartbeats 0

lemma equation_of_affine (A B x y : ℂ) (hy : y≠0)
    (he : y^2=x^3+A*x+B) : equation A B (-x/y) (1/y)=0 := by
  unfold equation
  field_simp
  linear_combination he

lemma short_affine_equation (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    yCoord tau z^2=xCoord tau z^3+
      (ModularWeierstrass318.curve tau).a₄*xCoord tau z+
      (ModularWeierstrass318.curve tau).a₆ := by
  convert normalized_weierstrass_equation tau z hz using 1 <;>
    simp [ModularWeierstrass318.curve,NormalizedWeierstrass318.model] <;> ring

/-- The actual analytically filled projective coordinates solve the actual cubic,
including at the point at infinity. -/
theorem equation_germ (tau : UpperHalfPlane) :
    ∀ᶠ z in 𝓝 (0:ℂ), equation (ModularWeierstrass318.curve tau).a₄
      (ModularWeierstrass318.curve tau).a₆ (t tau z) (v tau z)=0 := by
  have hreg : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ (periods tau).lattice := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((periods tau).compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with z hz hn
    simp only [Set.mem_compl_iff,Set.mem_sdiff,SetLike.mem_coe,Set.mem_singleton_iff] at hz hn ⊢
    aesop
  have he : ∀ᶠ z in 𝓝[≠] (0:ℂ), equation (ModularWeierstrass318.curve tau).a₄
      (ModularWeierstrass318.curve tau).a₆ (t tau z) (v tau z)=0 := by
    filter_upwards [coordinates_eventually tau,hreg] with z hz hzr
    rw [hz.2.1,hz.2.2]
    exact equation_of_affine _ _ _ _ hz.1 (short_affine_equation tau z hzr)
  have h := eventually_nhdsWithin_iff.mp he
  filter_upwards [h] with z hz
  by_cases hz0 : z=0
  · simp [hz0,t_zero,v_zero,equation]
  · exact hz (by simpa using hz0)

end ActualInfinityEquation318
