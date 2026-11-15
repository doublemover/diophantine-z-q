module
public import ActualMovingSigmaConvergence318
public section
noncomputable section
namespace ActualFiniteCharacterBoundary318
open scoped BigOperators Topology
open Filter ActualModFourSieveCharacter318 ActualModFourLFunctionBoundary318
open ActualCharacterFiniteLogControl318 ActualMovingBoundaryPrimeTail318
open ActualComplexEulerReal318 ActualMovingSigmaConvergence318
set_option maxHeartbeats 20000000

lemma prefix_subset (N M : ℕ) (hNM : N≤M) : Nat.primesBelow N⊆Nat.primesBelow M := by
  intro p hp
  have hh := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨hh.1.trans_le hNM,hh.2⟩
lemma actual_tail_primes (N M : ℕ) :
    ∀p∈Nat.primesBelow M \ Nat.primesBelow N,p.Prime ∧ N≤p := by
  intro p hp
  have hh := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesBelow hh.1
  refine ⟨hprime,?_⟩
  by_contra h
  exact hh.2 (Nat.mem_primesBelow.mpr ⟨by omega,hprime⟩)
lemma actual_prefix_tail_identity (σ : ℝ) (N M : ℕ) (hNM : N≤M) :
    finiteEuler σ (Nat.primesBelow M)=
      finiteEuler σ (Nat.primesBelow M \ Nat.primesBelow N)*finiteEuler σ (Nat.primesBelow N) :=
  (Finset.prod_sdiff (f := fun p => (1-realCharacter p*(p:ℝ)^(-σ))⁻¹)
    (prefix_subset N M hNM)).symm

/-- The true sigma>1 L-limit is consumed AFTER fixing the moving
exponent at the original N. The prime-cutoff limit M then uses the
uniform tail estimate. There is no exchange of these two limits. -/
theorem actual_L_norm_le_prefix (N : ℕ) (hN : 1<N) :
    ‖DirichletCharacter.LFunction complexCharacter (sigma N:ℂ)‖≤
      finiteEuler (sigma N) (Nat.primesBelow N)*Real.exp tailConstant := by
  have hσ := sigma_gt_one N hN
  have ht := actual_real_euler_limit (sigma N) hσ
  have he : ∀ᶠ M : ℕ in atTop,
      finiteEuler (sigma N) (Nat.primesBelow M)≤
        finiteEuler (sigma N) (Nat.primesBelow N)*Real.exp tailConstant := by
    filter_upwards [eventually_ge_atTop N] with M hM
    let S := Nat.primesBelow M \ Nat.primesBelow N
    have hs := actual_tail_primes N M
    have hlog := actual_finite_tail N hN S hs
    rw [←actual_finite_log (sigma N) hσ.le S (fun p hp => (hs p hp).1)] at hlog
    have hp := finite_euler_pos (sigma N) hσ.le S (fun p hp => (hs p hp).1)
    have hbound := Real.exp_le_exp.mpr (abs_le.mp hlog).2
    rw [Real.exp_log hp] at hbound
    rw [actual_prefix_tail_identity _ N M hM]
    have hpref := (finite_euler_pos (sigma N) hσ.le (Nat.primesBelow N)
      (fun p hp => Nat.prime_of_mem_primesBelow hp)).le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbound hpref
  exact le_of_tendsto ht he

lemma actual_prefix_shift (N : ℕ) (hN : 1<N) :
    finiteEuler (sigma N) (Nat.primesBelow N)≤
      finiteEuler 1 (Nat.primesBelow N)*Real.exp shiftConstant := by
  have hs (p : ℕ) (hp : p∈Nat.primesBelow N) : p.Prime ∧ p≤N :=
    ⟨Nat.prime_of_mem_primesBelow hp,(Nat.lt_of_mem_primesBelow hp).le⟩
  have hl := actual_finite_shift N hN (Nat.primesBelow N) hs
  rw [←actual_finite_log 1 le_rfl _ (fun p hp => (hs p hp).1),
    ←actual_finite_log (sigma N) (sigma_gt_one N hN).le _ (fun p hp => (hs p hp).1)] at hl
  have hup : Real.log (finiteEuler (sigma N) (Nat.primesBelow N))≤
      Real.log (finiteEuler 1 (Nat.primesBelow N))+shiftConstant := by
    linarith [(abs_le.mp hl).1]
  have hh := Real.exp_le_exp.mpr hup
  rw [Real.exp_add,Real.exp_log (finite_euler_pos 1 le_rfl _ (fun p hp => (hs p hp).1)),
    Real.exp_log (finite_euler_pos (sigma N) (sigma_gt_one N hN).le _ (fun p hp => (hs p hp).1))] at hh
  exact hh

@[expose] def boundaryLower : ℝ := boundarySize/(2*Real.exp (shiftConstant+tailConstant))
lemma boundary_lower_pos : 0<boundaryLower :=
  div_pos boundary_size_pos (mul_pos (by norm_num) (Real.exp_pos _))

/-- A positive lower bound for the finite character Euler products AT1,
derived from the genuine nonzero L-boundary through quantitative
finite shifts and tails. This is NOT a claim of product convergence. -/
theorem actual_eventual_character_lower :
    ∃ N₀ : ℕ,2≤N₀ ∧ ∀ N,N₀≤N →
      boundaryLower≤finiteEuler 1 (Nat.primesBelow N) := by
  obtain ⟨N₀,h2,hL⟩ := actual_moving_L_lower
  refine ⟨N₀,h2,?_⟩
  intro N hN
  have hn : 1<N := by omega
  have hnorm := actual_L_norm_le_prefix N hn
  have hshift := mul_le_mul_of_nonneg_right (actual_prefix_shift N hn) (Real.exp_pos tailConstant).le
  have he : (finiteEuler 1 (Nat.primesBelow N)*Real.exp shiftConstant)*Real.exp tailConstant=
      finiteEuler 1 (Nat.primesBelow N)*Real.exp (shiftConstant+tailConstant) := by
    rw [Real.exp_add,mul_assoc]
  rw [he] at hshift
  have hbound := (hL N hN).trans (hnorm.trans hshift)
  unfold boundaryLower
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.exp_pos _))).mpr
  nlinarith only [hbound]

end ActualFiniteCharacterBoundary318
