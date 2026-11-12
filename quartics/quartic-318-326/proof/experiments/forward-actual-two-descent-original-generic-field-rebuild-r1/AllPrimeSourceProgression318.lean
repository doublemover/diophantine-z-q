module
public import ActualInertOrbitEntry318
public import InertHensel318
public section
noncomputable section
namespace AllPrimeSourceProgression318
open ActualOrbitLocalFilter318 ActualOrbitTranslatedAccess318 SourceLocalProgression318
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- Every odd prime is covered: an actual residue square lifts to the two
split embeddings, while its negation selects the original inert completion.
Neither route assumes an orbit-entry modulus or good reduction. -/
theorem odd_error_bounds (p : ℕ) [Fact p.Prime] (hp : p≠2) :
    ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
      ‖error p ((p:ℤ)^e*N*m)‖≤((p:ℝ)⁻¹)^e := by
  by_cases hs : ∃ x : ZMod p, x^2=2
  · have htwo : ¬p∣2 := by
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).mp h with he|he
      · exact (Fact.out : p.Prime).ne_one he
      · exact hp he
    obtain ⟨ρ,hρ⟩ := InertHensel318.square_root_lift p htwo hs
    exact GeneralSplitDetectorAccess318.error_bounds p hp ρ hρ
  · exact ActualInertOrbitEntry318.error_bounds p hs

lemma odd_identity_access (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (U : Set (Fin 4 → ℚ_[p])) (hU : U∈𝓝 0) :
    ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, error p ((L:ℤ)*m)∈U := by
  obtain ⟨N,hN,hbound⟩ := odd_error_bounds p hp
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have hprime : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨e,he⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hprime)
  refine ⟨p^e*N,Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hN,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_zero_right]
  simpa only [Nat.cast_mul,Nat.cast_pow] using (hbound e m).trans_lt he

/-- Actual affine index continuity at every rational prime. The ramified
prime2 uses its earlier exact generator computation; all odd primes use the
constructed compact-quotient entry and actual rational coordinate recovery. -/
theorem actual_chart (p : ℕ) [Fact p.Prime] (a b h₀ : ℤ) :
    LocalIndexRegularity318.Regular h₀ (fun h => error p (a+b*h)) := by
  by_cases hp : p=2
  · subst p
    exact LocalIndexRegularity318.actual_chart 2 two_error_bound a b h₀
  · intro U hU
    have ht : (translate p (a+b*h₀)) ⁻¹' U∈𝓝 (0 : Fin 4 → ℚ_[p]) :=
      (translate_continuousAt p (a+b*h₀)) (by simpa only [translate_zero] using hU)
    obtain ⟨L,hL,haccess⟩ := odd_identity_access p hp _ ht
    refine ⟨L,hL,fun m => ?_⟩
    have hm := haccess (b*m)
    have hi : a+b*(h₀+(L:ℤ)*m)=a+b*h₀+(L:ℤ)*(b*m) := by ring
    rw [hi]
    simpa only [Set.mem_preimage,translate_error] using hm

/-- The original full146 detector coefficient family and all three pole
coordinates are now locally prepared at an arbitrary prime. Only the actual
admissible center/labels and the later depth of the contact parameter remain
inputs; no local recurrence or modulus is assumed. -/
theorem source_preparation (p : ℕ) [Fact p.Prime]
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ M : ℕ) (hM : 0<M) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ)))
    (A : ℤ) (hA : 0≤A) :
    ∃ L : ℕ, ∃ N : ℤ, 0<L ∧ M∣L ∧ Prepared p q labels h₀ L N A := by
  obtain ⟨L,N,hL,hprep⟩ := prepared_progression p (actual_chart p)
    q labels hn h₀ hzero hone hg A hA
  refine ⟨M*L,N,Nat.mul_pos hM hL,dvd_mul_right _ _,?_⟩
  exact Prepared.of_dvd p q labels h₀ L (M*L) N A hprep (dvd_mul_left _ _)

/-- A finite family of actual primes is prepared with one positive modulus,
retaining any earlier modulus M and the same original center. Thresholds
and modulus are chosen before the later contact parameters and final h.
No coprimality between these local moduli is required. -/
theorem finite_preparation {ι : Type*} [Fintype ι] (p : ι → ℕ)
    [∀ i, Fact (p i).Prime]
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ M : ℕ) (hM : 0<M) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ)))
    (A : ι → ℤ) (hA : ∀ i, 0≤A i) :
    ∃ L : ℕ, ∃ N : ι → ℤ, 0<L ∧ M∣L ∧
      ∀ i, Prepared (p i) q labels h₀ L (N i) (A i) := by
  classical
  have he : ∀ i, ∃ L : ℕ, ∃ N : ℤ, 0<L ∧ Prepared (p i) q labels h₀ L N (A i) :=
    fun i => prepared_progression (p i) (actual_chart (p i))
      q labels hn h₀ hzero hone hg (A i) (hA i)
  choose L N hL hprep using he
  let J := ∏ i, L i
  refine ⟨M*J,N,Nat.mul_pos hM (Finset.prod_pos (fun i _ => hL i)),dvd_mul_right _ _,?_⟩
  intro i
  exact Prepared.of_dvd (p i) q labels h₀ (L i) (M*J) (N i) (A i) (hprep i)
    ((Finset.dvd_prod_of_mem L (Finset.mem_univ i)).trans (dvd_mul_left J M))

end AllPrimeSourceProgression318
