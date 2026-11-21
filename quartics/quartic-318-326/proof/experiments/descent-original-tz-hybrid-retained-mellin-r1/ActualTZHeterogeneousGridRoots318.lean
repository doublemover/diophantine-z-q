module
public import ActualTZProductResidueDominance318
public section
noncomputable section
namespace ActualTZHeterogeneousGridRoots318
open scoped BigOperators
open ActualTZProductResidueDominance318
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]

@[expose] def roots (S : Fin n→Finset F) (p : MvPolynomial (Fin n) F) : Finset (Fin n→F) :=
  (Fintype.piFinset S).filter (fun z=>MvPolynomial.eval z p=0)

/-- Actual heterogeneous finite-box Schwartz–Zippel, independently
of how the ambient residue/fibre probabilities were produced.
Near-uniformity uses an explicit factor A^n. -/
theorem weighted_roots (S : Fin n→Finset F) (p : MvPolynomial (Fin n) F) (hp : p≠0)
    (m : Fin n→F→ℚ≥0) (A : ℚ≥0)
    (hM : ∀ i x,x∈S i→m i x≤A/((S i).card:ℚ≥0)) :
    (∑ z∈roots S p,∏ i : Fin n,m i (z i))≤
      A^n*(∑ i : Fin n,((p.degreeOf i:ℕ):ℚ≥0)/((S i).card:ℚ≥0)) := by
  refine (subbox_mass S (roots S p) (Finset.filter_subset _ _) m A hM).trans ?_
  exact mul_le_mul_of_nonneg_left (MvPolynomial.schwartz_zippel_sum_degreeOf hp S) (zero_le _)

/-- Keep exact separate coordinate supports. The sacrificial factor
n here is harmless (fixed original finite complexity), avoiding an
extra degree-monomial normal form. -/
theorem weighted_degree (S : Fin n→Finset F) (p : MvPolynomial (Fin n) F) (hp : p≠0)
    (d K : ℕ) (hd : p.totalDegree≤d) (hK : 0<K) (hS : ∀ i,K≤(S i).card)
    (m : Fin n→F→ℚ≥0) (A : ℚ≥0)
    (hM : ∀ i x,x∈S i→m i x≤A/((S i).card:ℚ≥0)) :
    (∑ z∈roots S p,∏ i : Fin n,m i (z i))≤ A^n*((n:ℚ≥0)*((d:ℚ≥0)/K)) := by
  apply (weighted_roots S p hp m A hM).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le _)
  calc
    _ ≤ ∑ _i : Fin n,(d:ℚ≥0)/K := by
      apply Finset.sum_le_sum
      intro i _
      have hSd : (p.degreeOf i:ℚ≥0)≤(d:ℚ≥0) := by
        exact_mod_cast (MvPolynomial.degreeOf_le_totalDegree p i).trans hd
      have hSK : (K:ℚ≥0)≤((S i).card:ℚ≥0) := by exact_mod_cast hS i
      have hK' : (0:ℚ≥0)<K := by exact_mod_cast hK
      exact div_le_div₀ (zero_le _) hSd hK' hSK
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end ActualTZHeterogeneousGridRoots318
