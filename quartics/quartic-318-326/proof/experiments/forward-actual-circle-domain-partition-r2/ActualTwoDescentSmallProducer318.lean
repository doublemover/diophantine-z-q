module
public import ActualTwoDescentSmallPrimeAssembly318
public section
noncomputable section
namespace ActualTwoDescentSmallProducer318
open ActualTwoDescentSmallPrimeAssembly318 ActualTwoDescentSmallPattern318
open ActualTwoDescentSmallCore318 ActualTwoDescentPrimeFamily318
open ActualTwoDescentFamilyProducts318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentMatrixCompletion318
open ActualTwoDescentLocalCoefficientBound318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- All finite arithmetic conclusions for the same first twist. The
actual core and beta-row conditions are conclusions, not input fields. -/
structure SmallConclusion (d : ℕ) (p : Index d → ℕ) (N : ℕ) : Prop where
  pattern : Pattern d p
  residue : ((∏ i, p i : ℕ) : ZMod 12)=11
  squarefree : Squarefree (∏ i, p i)
  large : N < ∏ i, p i
  beta_kernel : laplacian p *ᵥ beta d=0
  core_unit : IsUnit (fun i j => sharp p (selector d) (some i) (some j) :
    Matrix (CoreIndex d) (CoreIndex d) (ZMod 2))
  kernel : ∀ x, laplacian p *ᵥ x=0 ↔
    ∃ c e : ZMod 2, x=c • ones (Index d)+e • beta d
  lambda_excluded : ∀ x, laplacian p *ᵥ x ≠ lambda p
  local_coefficients : ∀ u v δ,
    laplacian p *ᵥ u+Matrix.diagonal (lambda p) *ᵥ v=δ • lambda p →
    (laplacian p+Matrix.diagonal (parity p)) *ᵥ v=0 →
    dotProduct (lambda p+parity p) v=0 →
    δ=0 ∧ v=0 ∧ ∃ c e : ZMod 2, u=c • ones (Index d)+e • beta d

/-- Produce the entire first-twist arithmetic package directly from the
original beta support17mod24. No suitable auxiliary primes, symbol pattern,
beta-kernel condition, nonsingular matrix, or local coefficient bound is
assumed. This does not assert a Selmer or rational-point existence bridge. -/
theorem actual_small_producer (d : ℕ) (q : BetaIndex d → ℕ)
    [∀ b, Fact (q b).Prime] (hq : Function.Injective q)
    (hβ : ((∏ b, q b : ℕ) : ZMod 24)=17) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ F : Family d q forbidden N, SmallConclusion d (assembled F) N := by
  have hβ12 : ((∏ b, q b : ℕ) : ZMod 12)=5 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hβ
    norm_num only [map_natCast,map_ofNat] at h
    exact h
  have hprod : Nat.Coprime (∏ b, q b) 12 := by
    apply (ZMod.isUnit_iff_coprime (∏ b, q b) 12).mp
    rw [hβ12]
    exact (ZMod.unitOfCoprime 5 (by decide)).isUnit
  have hqc : ∀ b, Nat.Coprime (q b) 12 := by
    intro b
    exact hprod.of_dvd_left (Finset.dvd_prod_of_mem q (Finset.mem_univ b))
  have hq2 : ∀ b, q b ≠ 2 := by
    intro b he
    have h := hqc b
    rw [he] at h
    norm_num at h
  obtain ⟨F⟩ := actual_finite_family q hq hqc hq2 (prescribedBits d) (fun _ _ => false)
    (fun k => decide (k=d)) forbidden N (d+1)
  have hd := assembled_injective F hq
  have hc := assembled_coprime F hqc
  have hp2 : ∀ i, assembled F i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp3 : ∀ i, assembled F i ≠ 3 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hn : ((∏ i, assembled F i : ℕ) : ZMod 12)=11 := by
    rw [assembled_product,Nat.cast_mul,hβ12,actual_multiplier_residue d F]
    norm_num
  have H := actual_assembled_pattern F hq hqc
  have hsquare : Squarefree (∏ i, assembled F i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.coprime_primes (Fact.out : (assembled F i).Prime)
        (Fact.out : (assembled F j).Prime)).mpr
      exact fun he => hij (hd he)
    · intro i _
      exact (Fact.out : (assembled F i).Prime).squarefree
  have hpos : 0 < ∏ i, assembled F i := by
    apply Finset.prod_pos
    intro i _
    exact (Fact.out : (assembled F i).Prime).pos
  have hlarge : N < ∏ i, assembled F i := by
    have hN : N < assembled F none := lt_of_le_of_lt (le_max_left _ _) (F.large (Fin.last d))
    apply lt_of_lt_of_le hN
    exact Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem (assembled F) (Finset.mem_univ none))
  have hb := actual_small_beta_kernel d (assembled F) hd hp2 hn H
  have hu := actual_small_core_unit d (assembled F) hd hp2 hp3 hn H
  obtain ⟨hk,himage⟩ := actual_small_kernel d (assembled F) hd hp2 hp3 hn H
  refine ⟨F,⟨H,hn,hsquare,hlarge,hb,hu,hk,himage,?_⟩⟩
  intro u v δ hfirst hsecond hthird
  exact actual_local_coefficient_bound (assembled F) hd hp2 hp3 hn (selector d) (beta d)
    (selector_sum d) hb (selector_beta d) hu u v δ hfirst hsecond hthird

end ActualTwoDescentSmallProducer318
