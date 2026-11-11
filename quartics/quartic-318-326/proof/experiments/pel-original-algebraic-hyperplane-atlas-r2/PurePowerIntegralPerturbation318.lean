module
public import MonomialDegreeFiltration318
public import PurePowerReductionFiniteAlgebra318
public section
noncomputable section
namespace PurePowerIntegralPerturbation318
open PurePowerReductionFiniteSpan318 MonomialDegreeFiltration318
variable {ι R A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]

/-- A monic integral equation for x_i^M-r with coefficients of bounded
old-coordinate degree produces the exact pure-power reduction required
for whole module finiteness. The strict inequality D<M is the sole
leading-degree dominance requirement. -/
theorem reduction (x : ι → A) (i : ι) (M D e : ℕ) (r : R)
    (c : ℕ → A) (hD : D < M)
    (hc : ∀ k < e+1, c k ∈ piece (R:=R) x D)
    (hrel : (x i^M-algebraMap R A r)^(e+1) +
      ∑ k ∈ Finset.range (e+1), c k*(x i^M-algebraMap R A r)^k = 0) :
    x i ^ (M*(e+1)) ∈ Submodule.span R
      {y : A | ∃ d : ι → ℕ, weight d < M*(e+1) ∧ monomial x d = y} := by
  let a := x i^M-algebraMap R A r
  let B := D+M*e
  have ha : a ∈ piece (R:=R) x M :=
    (piece x M).sub_mem (generator_power_mem x i M) (scalar_mem x r M)
  have hsum : (∑ k ∈ Finset.range (e+1), c k*a^k) ∈ piece (R:=R) x B := by
    apply Submodule.sum_mem
    intro k hk
    have hk' : k < e+1 := Finset.mem_range.mp hk
    exact mono x (Nat.add_le_add_left
      (Nat.mul_le_mul_left M (Nat.le_of_lt_succ hk')) D)
      (mul_mem x (hc k hk') (pow_mem x ha k))
  have hpow : a^(e+1) ∈ piece (R:=R) x B := by
    have heq : a^(e+1) = -(∑ k ∈ Finset.range (e+1), c k*a^k) :=
      eq_neg_of_add_eq_zero_left hrel
    rw [heq]
    exact (piece x B).neg_mem hsum
  have hdiff : a^(e+1)-(x i^M)^(e+1) ∈ piece (R:=R) x B :=
    mono x (by dsimp [B]; omega) (power_difference_mem x i M r e)
  have hfull : x i ^ (M*(e+1)) ∈ piece (R:=R) x B := by
    rw [pow_mul]
    have heq : (x i^M)^(e+1) = a^(e+1)-(a^(e+1)-(x i^M)^(e+1)) := by ring
    rw [heq]
    exact (piece x B).sub_mem hpow hdiff
  apply (Submodule.span_mono (R:=R) (s:={y : A | ∃ d : ι → ℕ,
    weight d ≤ B ∧ monomial x d = y}) (t:={y : A | ∃ d : ι → ℕ,
    weight d < M*(e+1) ∧ monomial x d = y}) ?_) hfull
  rintro y ⟨d,hd,rfl⟩
  exact ⟨d,by dsimp [B] at hd; nlinarith,rfl⟩

/-- A simultaneous system of these actual monic equations makes the
whole original generated algebra finite over the specified new base. -/
theorem finite_whole (x : ι → A) (M D : ℕ) (r : ι → R) (e : ι → ℕ)
    (c : ι → ℕ → A) (hD : D < M)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (hc : ∀ i k, k < e i+1 → c i k ∈ piece (R:=R) x D)
    (hrel : ∀ i, (x i^M-algebraMap R A (r i))^(e i+1) +
      ∑ k ∈ Finset.range (e i+1), c i k*(x i^M-algebraMap R A (r i))^k = 0) :
    Module.Finite R A :=
  PurePowerReductionFiniteAlgebra318.finite_whole x (fun i => M*(e i+1)) hgen
    (fun i => reduction x i M D (e i) (r i) (c i) hD (hc i) (hrel i))
end PurePowerIntegralPerturbation318
