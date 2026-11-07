module
public import ExceptionalNegativity318
public import CuspHeight318
public import FiniteDivisorArithmetic318
public section
noncomputable section
namespace SourceFiniteDivisor318
open Matrix NumberField
set_option maxHeartbeats 0

theorem branch_prime_card (N:ℕ) (hN:1≤N) :
    ((6*N).primeFactors.card:ℝ)≤Real.log (6*(N:ℝ))/Real.log 2 := by
  have hnp : 0<6*N := by omega
  have hprod : 2^(6*N).primeFactors.card≤∏p∈(6*N).primeFactors,p := by
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod (fun p hp=> (Nat.prime_of_mem_primeFactors hp).two_le)
  have hdvd := Nat.prod_primeFactors_dvd (6*N)
  have hle : 2^(6*N).primeFactors.card≤6*N := hprod.trans (Nat.le_of_dvd hnp hdvd)
  have hleR : (2:ℝ)^(6*N).primeFactors.card≤6*(N:ℝ) := by exact_mod_cast hle
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(6*N).primeFactors.card) hleR
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl

theorem vertical_budget (d N:ℕ) (hd:1≤d) (hN:1≤N) :
    (∑p∈(6*N).primeFactors,(⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊:ℝ)*Real.log p)
      ≤ Real.log (6*(N:ℝ))*Real.log d/Real.log 2 := by
  have hsum := FiniteDivisorArithmetic318.vertical_log_bound (6*N).primeFactors
    (fun p hp=>Nat.prime_of_mem_primeFactors hp) d (by omega)
  have hb := mul_le_mul_of_nonneg_right (branch_prime_card N hN)
    (Real.log_nonneg (show (1:ℝ)≤d by exact_mod_cast hd))
  calc
    _ ≤ ((6*N).primeFactors.card:ℝ)*Real.log d := hsum
    _ ≤ (Real.log (6*(N:ℝ))/Real.log 2)*Real.log d := hb
    _ = _ := by ring

/-- The finite-place bound is derived from the actual exceptional matrix,
local nonexceptional domination and pullback/section intersection formula.
The final canonical intersection bound itself is not assumed. -/
theorem canonical_section_bound {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M:Matrix ι ι ℝ) (hM:(-M).PosDef) (hoff:∀i j,i≠j → 0≤M i j)
    (C:Matrix ι κ ℝ) (hC:∀i j,0≤C i j)
    (DI KI:ι→ℝ) (DJ KJ:κ→ℝ) (hlocal:∀j,KJ j≤DJ j)
    (hz:∀i,(M *ᵥ (DI-KI)) i+(C *ᵥ (DJ-KJ)) i≤0)
    (sI:ι→ℝ) (sJ:κ→ℝ) (hsI:∀i,0≤sI i) (hsJ:∀j,0≤sJ j)
    (n d N:ℕ) (hn:2≤n) (hd:1≤d) (hN:1≤N)
    (hprojection:(∑i,DI i*sI i)+(∑j,DJ j*sJ j)≤
      FiniteDivisorArithmetic318.horizontalContact (1/(n:ℚ))+
      2*(∑p∈(6*N).primeFactors,(⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊:ℝ)*Real.log p)) :
    (∑i,KI i*sI i)+(∑j,KJ j*sJ j)≤
      3*absLogHeight₁ (1/(n:ℚ))+2*Real.log (6*(N:ℝ))*Real.log d/Real.log 2 := by
  have he := ExceptionalNegativity318.canonical_domination_with_outside M hM hoff C hC
    (DJ-KJ) (by intro j; exact sub_nonneg.mpr (hlocal j)) DI KI hz
  have hI : (∑i,KI i*sI i)≤∑i,DI i*sI i := by
    exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (he i) (hsI i))
  have hJ : (∑j,KJ j*sJ j)≤∑j,DJ j*sJ j := by
    exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (hlocal j) (hsJ j))
  have hh := FiniteDivisorArithmetic318.reciprocal_horizontal_bound n hn
  have hv := vertical_budget d N hd hN
  have heq : 2*(Real.log (6*(N:ℝ))*Real.log d/Real.log 2)=2*Real.log (6*(N:ℝ))*Real.log d/Real.log 2 := by ring
  linarith

end SourceFiniteDivisor318
#print axioms SourceFiniteDivisor318.branch_prime_card
#print axioms SourceFiniteDivisor318.vertical_budget
#print axioms SourceFiniteDivisor318.canonical_section_bound
