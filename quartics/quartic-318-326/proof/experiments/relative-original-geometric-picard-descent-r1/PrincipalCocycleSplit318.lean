module
public import PrincipalFractionClearing318
public import Mathlib.RingTheory.Spectrum.Prime.Topology

public section
noncomputable section
namespace PrincipalCocycleSplit318
open PrincipalFractionClearing318
open scoped BigOperators
set_option maxHeartbeats 600000
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι]

omit [IsDomain R] in
/-- A principal cover remains a unit-ideal cover after any common power. -/
theorem power_coefficients (f : ι → R) (h : Ideal.span (Set.range f) = ⊤) (N : ℕ) :
    ∃ a : ι → R, ∑ j, a j * f j ^ N = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  have hN := Ideal.span_pow_eq_top (Set.range f) h N
  rw [← Set.range_comp] at hN
  change Ideal.span (Set.range fun i => f i ^ N) = ⊤ at hN
  rw [hN]
  trivial

/-- Actual regular rational functions on every overlap of a finite principal cover
have zero additive Cech H1: every additive cocycle is the difference of actual local sections. -/
theorem split (f : ι → R) (hf : ∀ i, f i ≠ 0)
    (hcover : Ideal.span (Set.range f) = ⊤)
    (c : ι → ι → K)
    (hregular : ∀ i j, c i j ∈ away (f i*f j) (mul_ne_zero (hf i) (hf j)))
    (hcocycle : ∀ i j k, c i j + c j k = c i k) :
    ∃ b : ι → K, (∀ i, b i ∈ away (f i) (hf i)) ∧ ∀ i j, c i j = b i-b j := by
  classical
  obtain ⟨N,hN⟩ := clear_finite f hf c hregular
  obtain ⟨a,ha⟩ := power_coefficients f hcover N
  let w (j : ι) : K := algebraMap R K (a j) * algebraMap R K (f j) ^ N
  have hw : ∑ j, w j = 1 := by
    have h := congrArg (algebraMap R K) ha
    simpa only [map_sum, map_mul, map_pow, map_one, w] using h
  let b (i : ι) : K := ∑ j, w j * c i j
  refine ⟨b,fun i => ?_,fun i k => ?_⟩
  · apply (away (K:=K) (f i) (hf i)).sum_mem
    intro j hj
    change algebraMap R K (a j) * algebraMap R K (f j) ^ N * c i j ∈ _
    rw [mul_assoc]
    exact (away (f i) (hf i)).mul_mem ((away (f i) (hf i)).algebraMap_mem _) (hN i j)
  · have h (j : ι) : c i j-c k j = c i k := by
      exact sub_eq_iff_eq_add.mpr (hcocycle i k j).symm
    change c i k = (∑ j, w j*c i j)-(∑ j, w j*c k j)
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, h]
    rw [← Finset.sum_mul, hw, one_mul]

/-- The same statement takes the actual topological principal-cover hypothesis. -/
theorem split_of_principal_cover (f : ι → R) (hf : ∀ i, f i ≠ 0)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (c : ι → ι → K)
    (hregular : ∀ i j, c i j ∈ away (f i*f j) (mul_ne_zero (hf i) (hf j)))
    (hcocycle : ∀ i j k, c i j+c j k=c i k) :
    ∃ b : ι → K, (∀ i, b i ∈ away (f i) (hf i)) ∧ ∀ i j, c i j=b i-b j :=
  split f hf (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover) c hregular hcocycle

end PrincipalCocycleSplit318
