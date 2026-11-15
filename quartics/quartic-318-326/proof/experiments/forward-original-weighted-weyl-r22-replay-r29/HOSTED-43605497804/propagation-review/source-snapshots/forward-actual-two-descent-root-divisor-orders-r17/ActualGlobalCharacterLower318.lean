module
public import ActualFiniteCharacterBoundary318
public section
noncomputable section
namespace ActualGlobalCharacterLower318
open scoped BigOperators
open ActualCharacterFiniteLogControl318 ActualFiniteCharacterBoundary318
set_option maxHeartbeats 16000000

lemma inverse_majorant_lower (x K : ℝ) (hx : 0<x) (hK : x⁻¹≤K) : 1/K≤x := by
  have hh := one_div_le_one_div_of_le (inv_pos.mpr hx) hK
  simpa only [one_div,inv_inv] using hh

/-- Genuine positive uniform lower bound over ALL actual prime
cutoffs, including the finitely many cutoffs before the L-boundary
threshold. The finite prefix is handled explicitly, not discarded. -/
theorem actual_global_character_lower :
    ∃ c : ℝ,0<c ∧ ∀ N,c≤finiteEuler 1 (Nat.primesBelow N) := by
  obtain ⟨N₀,_,hN₀⟩ := actual_eventual_character_lower
  let f := fun N => finiteEuler 1 (Nat.primesBelow N)
  have hf (N : ℕ) : 0<f N := finite_euler_pos 1 le_rfl _ (fun p hp => Nat.prime_of_mem_primesBelow hp)
  let A : ℝ := ∑ n∈Finset.range N₀,(f n)⁻¹
  have hA : 0≤A := Finset.sum_nonneg (fun n _ => (inv_pos.mpr (hf n)).le)
  let K : ℝ := boundaryLower⁻¹+1+A
  have hK : 0<K := by
    have hh := inv_pos.mpr boundary_lower_pos
    dsimp [K]
    linarith
  refine ⟨1/K,one_div_pos.mpr hK,?_⟩
  intro N
  by_cases hn : N₀≤N
  · have hB : boundaryLower⁻¹≤K := by dsimp [K];linarith
    exact (inverse_majorant_lower boundaryLower K boundary_lower_pos hB).trans (hN₀ N hn)
  · have hm : N∈Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hh : (f N)⁻¹≤A := Finset.single_le_sum (fun n _ => (inv_pos.mpr (hf n)).le) hm
    have hb : (f N)⁻¹≤K := by
      have hp := inv_pos.mpr boundary_lower_pos
      dsimp [K]
      linarith
    exact inverse_majorant_lower (f N) K (hf N) hb

end ActualGlobalCharacterLower318
