module
public import FourRootSignCoefficientExtraction318
public import Mathlib.LinearAlgebra.Finsupp.Span
public section
noncomputable section
namespace FourRootCoordinateMonomialSpanning318
open scoped BigOperators
open FourRootSignCoefficientExtraction318
open FourRootAffineCoordinateRing318
variable (b : Fin 4 → ℂ)
abbrev P := Polynomial ℂ
local instance : Algebra P (Ring b) := (Polynomial.aeval (coordinate b none)).toAlgebra

def rootMonomial (m : Mask) : Ring b := ∏ i, if m i then coordinate b (some i) else 1

def span : Submodule P (Ring b) := Submodule.span P (Set.range (rootMonomial b))
lemma monomial_mem (m : Mask) : rootMonomial b m ∈ span b :=
  Submodule.subset_span ⟨m,rfl⟩
lemma one_mem : (1 : Ring b) ∈ span b := by
  simpa [rootMonomial] using monomial_mem b (fun _ => false)
lemma scalar_mem (p : P) : algebraMap P (Ring b) p ∈ span b := by
  simpa only [Algebra.smul_def,mul_one] using (span b).smul_mem p (one_mem b)

lemma root_mul_monomial (m : Mask) (k : Fin 4) :
    rootMonomial b m * coordinate b (some k) =
      (if m k then Polynomial.X - Polynomial.C (b k) else 1) •
        rootMonomial b (Function.update m k (!(m k))) := by
  let rest := ∏ i ∈ (Finset.univ : Finset (Fin 4)).erase k,
    if m i then coordinate b (some i) else 1
  have hrest : (∏ i ∈ (Finset.univ : Finset (Fin 4)).erase k,
      if (Function.update m k (!(m k))) i then coordinate b (some i) else 1) = rest := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hm : rootMonomial b m = (if m k then coordinate b (some k) else 1) * rest := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
  have hn : rootMonomial b (Function.update m k (!(m k))) =
      (if !(m k) then coordinate b (some k) else 1) * rest := by
    unfold rootMonomial
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),hrest,Function.update_same]
  rw [hm,hn]
  cases hk : m k
  · simp [hk]
  · simp only [hk,Bool.not_true,ite_true,ite_false,one_mul,Algebra.smul_def]
    have hp : algebraMap P (Ring b) (Polynomial.X - Polynomial.C (b k)) =
        coordinate b none - algebraMap ℂ (Ring b) (b k) := by
      change Polynomial.aeval (coordinate b none) (Polynomial.X - Polynomial.C (b k)) = _
      simp
    rw [hp,← relation b k]
    ring

lemma mul_coordinate_mem (x : Ring b) (hx : x ∈ span b) (k : Option (Fin 4)) :
    x * coordinate b k ∈ span b := by
  cases k with
  | none =>
      have h := (span b).smul_mem Polynomial.X hx
      simpa only [Algebra.smul_def,Polynomial.aeval_X,mul_comm] using h
  | some k =>
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨m,rfl⟩ := hx
          rw [root_mul_monomial]
          exact (span b).smul_mem _ (monomial_mem b _)
      | zero => simpa using (span b).zero_mem
      | add x y hx hy hxi hyi =>
          simpa only [add_mul] using (span b).add_mem hxi hyi
      | smul p x hx hxi =>
          simpa only [Algebra.smul_def,mul_assoc] using (span b).smul_mem p hxi

/-- Spanning is proved on the literal polynomial quotient, not inferred
from its rank or a chosen generic field. -/
theorem all_mem (x : Ring b) : x ∈ span b := by
  induction x using Ideal.Quotient.inductionOn with
  | _ p =>
    induction p using MvPolynomial.induction_on with
    | C c =>
        have h := scalar_mem b (Polynomial.C c)
        exact h
    | add p q hp hq =>
        simpa only [map_add] using (span b).add_mem hp hq
    | mul_X p k hp =>
        simpa only [map_mul] using mul_coordinate_mem b _ hp k

/-- Exactly sixteen polynomial coefficients, with the original base
coordinate and literal four roots. -/
theorem decomposition (x : Ring b) :
    ∃ c : Mask → P, (∑ m, c m • rootMonomial b m) = x :=
  Submodule.mem_span_range_iff_exists_fun.mp (all_mem b x)
end FourRootCoordinateMonomialSpanning318
