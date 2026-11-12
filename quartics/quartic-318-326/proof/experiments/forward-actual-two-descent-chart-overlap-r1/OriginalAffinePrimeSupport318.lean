module
public import OriginalExceptionalAffineElimination318
public section
noncomputable section
namespace OriginalAffinePrimeSupport318
open TernaryQuadraticLineCover318 OriginalNormPointSieveTail318 OriginalAffineSieveEliminants318
open OriginalLargePrimeDivisorCount318
set_option maxHeartbeats 4500000

@[expose] def support (n m : ℤ) (Y : ℕ) := largeDivisors n Y ∪ largeDivisors m Y

lemma support_log_bound (n m : ℤ) (hn : n≠0) (hm : m≠0) (Y : ℕ) (hY : 1<Y)
    (N M : ℝ) (hN : |(n:ℝ)|≤N) (hM : |(m:ℝ)|≤M) :
    ((support n m Y).card:ℝ)*Real.log (Y:ℝ)≤Real.log N+Real.log M := by
  have hyR : (1:ℝ)<Y := by exact_mod_cast hY
  have hylog : 0≤Real.log (Y:ℝ) := (Real.log_pos hyR).le
  have hc : ((support n m Y).card:ℝ)≤
      ((largeDivisors n Y).card:ℝ)+((largeDivisors m Y).card:ℝ) := by
    exact_mod_cast Finset.card_union_le (largeDivisors n Y) (largeDivisors m Y)
  have hh := mul_le_mul_of_nonneg_right hc hylog
  have h1 := actual_large_divisor_height n hn Y hY N hN
  have h2 := actual_large_divisor_height m hm Y hY M hM
  nlinarith only [hh,h1,h2]

/-- Every prime obstruction anywhere on the ACTUAL integer affine fiber
is covered by the explicit finite support, with no leading-prime omission.
The two zero-value offsets are kept as explicit exclusions for the later
geometric zero-locus count. -/
theorem actual_affine_prime_cover (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (Y : ℕ)
    (hfirst : normEliminant side κ t a d false≠0)
    (hsecond : normEliminant side κ t a d true≠0)
    (h : ℤ) (p : ℕ) (hp : p.Prime) (hYp : Y<p)
    (ho : pointObstruction side κ t (affine a d h) p) :
    p∈support (normEliminant side κ t a d false) (normEliminant side κ t a d true) Y := by
  rcases obstruction_eliminates side κ t a d h p hp ho with hx|hz
  · exact Finset.mem_union_left _ ((mem_largeDivisors _ hfirst Y p).mpr ⟨hp,hx,hYp⟩)
  · exact Finset.mem_union_right _ ((mem_largeDivisors _ hsecond Y p).mpr ⟨hp,hz,hYp⟩)

/-- Exceptional t=-2 fibers have their own actual finite support. If both
transverse coefficients are nonzero, positivity supplies BOTH nonzero
eliminant inputs uniformly in the offset a. -/
theorem exceptional_affine_prime_cover (κ t : ℤ) (ht2 : t+2=0)
    (a d : Vector ℤ) (hdx : d.1≠0) (hdz : d.2.1≠0)
    (Y : ℕ) (h : ℤ) (p : ℕ) [Fact p.Prime] (ht : ¬(p:ℤ)∣t) (hYp : Y<p)
    (ho : pointObstruction true κ t (affine a d h) p) :
    p∈support (OriginalLinearNormEliminant318.eliminant t a.1 a.2.1 d.1 d.2.1)
      (OriginalLinearNormEliminant318.eliminant t a.2.1 a.1 d.2.1 d.1) Y := by
  have ht0 : t≠0 := by omega
  have hfirst := (OriginalLinearNormEliminant318.positive t a.1 a.2.1 d.1 d.2.1 ht0 hdx).ne'
  have hsecond := (OriginalLinearNormEliminant318.positive t a.2.1 a.1 d.2.1 d.1 ht0 hdz).ne'
  rcases OriginalExceptionalAffineElimination318.actual_exceptional_eliminates κ t ht2 a d h p ht ho with hx|hz
  · exact Finset.mem_union_left _ ((mem_largeDivisors _ hfirst Y p).mpr ⟨Fact.out,hx,hYp⟩)
  · exact Finset.mem_union_right _ ((mem_largeDivisors _ hsecond Y p).mpr ⟨Fact.out,hz,hYp⟩)

end OriginalAffinePrimeSupport318
