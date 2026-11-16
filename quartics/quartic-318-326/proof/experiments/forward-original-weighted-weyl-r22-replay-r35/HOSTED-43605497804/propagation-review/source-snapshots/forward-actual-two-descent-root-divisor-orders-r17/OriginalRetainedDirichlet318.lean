module
public import OriginalRetainedFamilyWeight318
public section
noncomputable section
namespace OriginalRetainedDirichlet318
open scoped BigOperators
open OriginalRetainedFamilyWeight318
set_option maxHeartbeats 7000000

@[expose] def dirichlet (κ : ℤ) (δ : ℝ) (n : ℕ) : ℝ := weight κ n*(n:ℝ)^(-δ)
@[expose] def ratio (δ : ℝ) (p : ℕ) : ℝ := (p:ℝ)^(-δ)
@[expose] def localFactor (κ : ℤ) (δ : ℝ) (p : ℕ) : ℝ :=
  1+primeWeight κ p*ratio δ p/(1-ratio δ p)

lemma nonneg (κ : ℤ) (δ : ℝ) (n : ℕ) : 0≤dirichlet κ δ n :=
  mul_nonneg (weight_nonneg κ n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
lemma at_one (κ : ℤ) (δ : ℝ) : dirichlet κ δ 1=1 := by simp [dirichlet,weight_one]
lemma at_zero (κ : ℤ) (δ : ℝ) : dirichlet κ δ 0=0 := by simp [dirichlet,weight_zero]

lemma coprime_mul (κ : ℤ) (δ : ℝ) {m n : ℕ} (h : m.Coprime n) :
    dirichlet κ δ (m*n)=dirichlet κ δ m*dirichlet κ δ n := by
  rw [dirichlet,weight_mul κ h,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  dsimp [dirichlet]
  ring

lemma prime_power (κ : ℤ) (δ : ℝ) (p e : ℕ) (hp : p.Prime) :
    dirichlet κ δ (p^(e+1))=primeWeight κ p*(ratio δ p)^(e+1) := by
  rw [dirichlet,weight_prime_power κ p e hp,Nat.cast_pow,
    ←Real.rpow_natCast_mul (Nat.cast_nonneg p)]
  rw [mul_comm ((e+1:ℕ):ℝ) (-δ),Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  rfl

lemma ratio_positive (δ : ℝ) (p : ℕ) (hp : p.Prime) : 0<ratio δ p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
lemma ratio_lt_one (δ : ℝ) (hδ : 0<δ) (p : ℕ) (hp : p.Prime) : ratio δ p<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
lemma localFactor_one_le (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (p : ℕ) (hp : p.Prime) :
    1≤localFactor κ δ p := by
  have hr := ratio_positive δ p hp
  have hr1 := ratio_lt_one δ hδ p hp
  have hw := primeWeight_nonneg κ p
  dsimp [localFactor]
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hw hr.le) (sub_pos.mpr hr1).le)

/-- Exact local Euler series of the ACTUAL retained-radical weight.
Unretained primes retain their whole geometric series, not merely one
factor or one power, so primes dividing2*kappa cannot disappear later. -/
theorem prime_series (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => dirichlet κ δ (p^e)) (localFactor κ δ p) := by
  let r := ratio δ p
  have hr0 : 0<r := ratio_positive δ p hp
  have hr1 : r<1 := ratio_lt_one δ hδ p hp
  have hgeom := hasSum_geometric_of_norm_lt_one (show ‖r‖<1 by simpa [Real.norm_eq_abs,abs_of_pos hr0] using hr1)
  have hshift : HasSum (fun e : ℕ => dirichlet κ δ (p^(e+1)))
      (primeWeight κ p*r/(1-r)) := by
    convert hgeom.mul_left (primeWeight κ p*r) using 1
    · funext e
      rw [prime_power κ δ p e hp,pow_succ]
      change primeWeight κ p*(r^e*r)=(primeWeight κ p*r)*r^e
      ring
    · simp only [div_eq_mul_inv]
  have hh := (hasSum_nat_add_iff 1).mp hshift
  simpa only [Finset.sum_range_one,pow_zero,at_one,localFactor,add_comm] using hh

lemma prime_norm_summable (κ : ℤ) (δ : ℝ) (hδ : 0<δ) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖dirichlet κ δ (p^e)‖) := by
  convert (prime_series κ δ hδ p hp).summable using 1
  funext e
  exact norm_of_nonneg (nonneg κ δ (p^e))

/-- The pinned finite-prime Euler theorem constructs the sum over all
integers supported on the ACTUAL finite prime range. Global summability
of this weighted Dirichlet series is NOT assumed. -/
theorem finite_euler (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (S : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers S => dirichlet κ δ n.1)
      (∏ p∈S.filter Nat.Prime, localFactor κ δ p) := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (at_one κ δ) (fun h => coprime_mul κ δ h) (prime_norm_summable κ δ hδ) S).2
  convert hh using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (prime_series κ δ hδ p (Finset.mem_filter.mp hp).2).tsum_eq.symm

end OriginalRetainedDirichlet318
