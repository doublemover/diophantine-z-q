module
public import ActualSplitOrbitEntry318
public import AllSmallPrimeProgression318
public section
noncomputable section
namespace GeneralSplitDetectorAccess318
open ConcreteG8Domain (K D pair)
open ValuativeOrbitBounds318
open ActualOrbitLocalFilter318 ActualOrbitTranslatedAccess318
open CoherentMultipleCharts318 (chartU chartV)
open scoped Topology
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime] (hp : p≠2)
include hp

lemma two_value : Padic.addValuation (2:ℚ_[p])=0 := by
  have hd : ¬p∣2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with he|he
    · exact (Fact.out : p.Prime).ne_one he
    · exact hp he
  have he := ConcretePadic318.rational_nat_unit p 2 hd
  rw [PadicDetectorCoefficients318.rational_embedding] at he
  simpa using he

lemma root_value (ρ : ℚ_[p]) (hρ : ρ^2=2) : Padic.addValuation ρ=0 := by
  have hn : ρ≠0 := by intro he; rw [he] at hρ; norm_num at hρ
  have he := congrArg Padic.addValuation hρ
  rw [Padic.addValuation.map_pow,Padic.addValuation.apply hn,two_value p hp,two_nsmul] at he
  have hi : ρ.valuation+ρ.valuation=0 := by exact_mod_cast he
  have hz : ρ.valuation=0 := by omega
  rw [Padic.addValuation.apply hn,hz] <;> rfl

lemma recover_coefficients (ρ : ℚ_[p]) (hρ : ρ^2=2) (r : ℤ) (x : K)
    (hpos : Bound (ConcretePadic318.place p ρ hρ) r x)
    (hn : Bound (ConcretePadic318.place p (-ρ) (ConcretePadic318.negative_root p ρ hρ)) r x) :
    (r:WithTop ℤ)≤ConcretePadic318.rationalPlace p x.re ∧
    (r:WithTop ℤ)≤ConcretePadic318.rationalPlace p x.im := by
  have hρ0 : ρ≠0 := by intro he; rw [he] at hρ; norm_num at hρ
  change Bound (ConcretePadic318.place p ρ hρ) r (pair x.re x.im) at hpos
  change Bound (ConcretePadic318.place p (-ρ) (ConcretePadic318.negative_root p ρ hρ)) r (pair x.re x.im) at hn
  rw [Bound,ConcretePadic318.place_pair] at hpos hn
  have hsum := bdiv Padic.addValuation (badd Padic.addValuation hpos hn) (two_value p hp)
  have hdiff := bdiv Padic.addValuation (bsub Padic.addValuation hpos hn)
    (show Padic.addValuation (2*ρ)=0 by rw [Padic.addValuation.map_mul,(two_value p hp),root_value p hp ρ hρ,zero_add])
  have hre : (((x.re:ℚ_[p])+(x.im:ℚ_[p])*ρ)+((x.re:ℚ_[p])+(x.im:ℚ_[p])*(-ρ)))/2=(x.re:ℚ_[p]) := by ring
  have him : (((x.re:ℚ_[p])+(x.im:ℚ_[p])*ρ)-((x.re:ℚ_[p])+(x.im:ℚ_[p])*(-ρ)))/(2*ρ)=(x.im:ℚ_[p]) := by
    field_simp [hρ0] <;> ring
  rw [hre] at hsum
  rw [him] at hdiff
  rw [PadicDetectorCoefficients318.rational_embedding,PadicDetectorCoefficients318.rational_embedding]
  exact ⟨hsum,hdiff⟩

/-- A constructed common entry modulus gives all four original rational
coefficient error bounds, uniformly over every later signed multiplier. -/
theorem error_bounds (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
      ‖error p ((p:ℤ)^e*N*m)‖≤((p:ℝ)⁻¹)^e := by
  obtain ⟨N,hN,hprecision⟩ := ActualSplitOrbitEntry318.conjugate_precision p ρ hρ
  refine ⟨N,hN,?_⟩
  intro e m
  obtain ⟨hpos,hneg⟩ := hprecision e m
  have hu := recover_coefficients p hp ρ hρ ((e:ℤ)+1) _ hpos.1 hneg.1
  have hv := recover_coefficients p hp ρ hρ ((e:ℤ)+1) _ hpos.2 hneg.2
  have hle : (e:WithTop ℤ)≤(((e:ℤ)+1:ℤ):WithTop ℤ) := by exact_mod_cast (show (e:ℤ)≤e+1 by omega)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  fin_cases j
  · exact norm_of_depth p e _ (le_trans hle hu.1)
  · exact norm_of_depth p e _ (le_trans hle hu.2)
  · exact norm_of_depth p e _ (le_trans hle hv.1)
  · exact norm_of_depth p e _ (le_trans hle hv.2)

lemma identity_access (ρ : ℚ_[p]) (hρ : ρ^2=2)
    (U : Set (Fin 4 → ℚ_[p])) (hU : U∈𝓝 0) :
    ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, error p ((L:ℤ)*m)∈U := by
  obtain ⟨N,hN,hbound⟩ := error_bounds p hp ρ hρ
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have hprime : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨e,he⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hprime)
  refine ⟨p^e*N,Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hN,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_zero_right]
  simpa only [Nat.cast_mul,Nat.cast_pow] using (hbound e m).trans_lt he

lemma translated_access (ρ : ℚ_[p]) (hρ : ρ^2=2) (n : ℤ)
    (U : Set (Fin 4 → ℚ_[p])) (hU : U∈𝓝 (error p n)) :
    ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, error p (n+(L:ℤ)*m)∈U := by
  have ht : (translate p n) ⁻¹' U∈𝓝 (0 : Fin 4 → ℚ_[p]) :=
    (translate_continuousAt p n) (by simpa only [translate_zero] using hU)
  obtain ⟨L,hL,haccess⟩ := identity_access p hp ρ hρ _ ht
  refine ⟨L,hL,fun m => ?_⟩
  simpa only [Set.mem_preimage,translate_error] using haccess m

/-- Actual affine index regularity at any odd split prime, including the
bad-reduction primes admitted by the exact short-curve argument. -/
lemma actual_chart (ρ : ℚ_[p]) (hρ : ρ^2=2) (a b h₀ : ℤ) :
    LocalIndexRegularity318.Regular h₀ (fun h => error p (a+b*h)) := by
  intro U hU
  obtain ⟨L,hL,haccess⟩ := translated_access p hp ρ hρ (a+b*h₀) U hU
  refine ⟨L,hL,fun m => ?_⟩
  have hi : a+b*(h₀+(L:ℤ)*m)=a+b*h₀+(L:ℤ)*(b*m) := by ring
  rw [hi]
  exact haccess (b*m)

/-- This is the original full146-coefficient, three-pole arithmetic
consumer. The local entry modulus is now produced at every odd split prime;
labels and admissible center still precede threshold and modulus, which
precede later contact parameters and the final compatible integer h. -/
theorem source_preparation (ρ : ℚ_[p]) (hρ : ρ^2=2)
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ M : ℕ) (hM : 0<M) (hzero : (h₀:ℤ)≠0) (hone : (h₀:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₀:ℤ)))
    (A : ℤ) (hA : 0<A) :
    ∃ L : ℕ, ∃ N : ℤ, 0<L ∧ M∣L ∧
      SourceLocalProgression318.Prepared p q labels h₀ L N A := by
  obtain ⟨L,N,hL,hprep⟩ := SourceLocalProgression318.prepared_progression p
    (actual_chart p hp ρ hρ) q labels hn h₀ hzero hone hg A hA.le
  refine ⟨M*L,N,Nat.mul_pos hM hL,dvd_mul_right _ _,?_⟩
  exact SourceLocalProgression318.Prepared.of_dvd p q labels h₀ L (M*L) N A hprep
    (dvd_mul_left _ _)

end GeneralSplitDetectorAccess318
