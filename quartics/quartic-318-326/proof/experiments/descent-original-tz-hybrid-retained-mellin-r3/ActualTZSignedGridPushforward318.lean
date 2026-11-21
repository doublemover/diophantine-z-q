module
public import ActualTZSignedAxisSupport318
public import ActualTZHeterogeneousGridRoots318
public section
noncomputable section
namespace ActualTZSignedGridPushforward318
open scoped BigOperators
open ActualTZSignedAxisSupport318 ActualTZHeterogeneousGridRoots318

variable {n p : ℕ} [NeZero p] [Fact p.Prime]

abbrev Grid (L : Fin n→ℕ) := (i : Fin n)→Fin (L i)

@[expose] def residue (L : Fin n→ℕ) (s : Fin n→ℤ) (t : Grid L) : Fin n→ZMod p :=
  fun i=>digit (s i) (t i).val

def probability (L : Fin n→ℕ) (s : Fin n→ℤ) (P : MvPolynomial (Fin n) (ZMod p)) : ℚ≥0 :=
  ∑ t : Grid L,if MvPolynomial.eval (residue L s t) P=0 then
    ∏ i : Fin n,1/(L i:ℚ≥0) else 0

private theorem fibre (L : Fin n→ℕ) (s : Fin n→ℤ) (t : Grid L) (z : Fin n→ZMod p) :
    (∏ i : Fin n,if digit (s i) (t i).val=z i then 1/(L i:ℚ≥0) else 0)=
      if residue L s t=z then (∏ i : Fin n,1/(L i:ℚ≥0)) else 0 := by
  classical
  by_cases h : residue L s t=z
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    exact if_pos (congrFun h i)
  · rw [if_neg h]
    have H : ∃ i,digit (s i) (t i).val≠z i := by
      by_contra hh
      apply h
      funext i
      by_contra hi
      exact hh ⟨i,hi⟩
    obtain ⟨i,hi⟩ := H
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

/-- Exact finite pushforward of the original independent *signed
interval* sample onto its independent residue product. The
underlying set in each axis is not replaced by all p residues in a
short interval, and no Cartesian multiplicities are lost. -/
theorem pushforward (L : Fin n→ℕ) (s : Fin n→ℤ) (P : MvPolynomial (Fin n) (ZMod p)) :
    probability L s P =
      ∑ z∈roots (fun i=>axis (p:=p) (L i) (s i)) P,
        ∏ i : Fin n,atom (L i) (s i) (z i) := by
  classical
  let S (i : Fin n) := axis (p:=p) (L i) (s i)
  let T := roots S P
  let w : ℚ≥0 := ∏ i : Fin n,1/(L i:ℚ≥0)
  have hMem (t : Grid L) : residue L s t∈T ↔ MvPolynomial.eval (residue L s t) P=0 := by
    rw [T,roots,Finset.mem_filter]
    refine ⟨And.right,fun h=>⟨?_,h⟩⟩
    exact Fintype.mem_piFinset.mpr (fun i=>digit_mem (L i) (s i) (t i))
  symm
  calc
    _ = ∑ z∈T,∑ t : Grid L,if residue L s t=z then w else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp_rw [atom_sum,Fintype.prod_sum,fibre]
    _ = ∑ t : Grid L,∑ z∈T,if residue L s t=z then w else 0 := Finset.sum_comm
    _ = _ := by
      unfold probability
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : MvPolynomial.eval (residue L s t) P=0
      · rw [if_pos ht,Finset.sum_eq_single_of_mem (residue L s t) ((hMem t).2 ht)]
        · simp
        · intro z _ hz; exact if_neg (Ne.symm hz)
      · rw [if_neg ht]
        apply Finset.sum_eq_zero
        intro z hz
        apply if_neg
        intro he
        exact ht ((hMem t).1 (he.symm ▸ hz))

/-- Actual signed grid nonexceptional prime marginal made directly
from the pinned heterogeneous Schwartz–Zippel theorem. Conditions
hP and hd refer to the MOD-p polynomial and must be supplied by the
existing literal translated coefficients; no generic extra donor. -/
theorem probability_le (L : Fin n→ℕ) (s : Fin n→ℤ) (M d : ℕ)
    (hM : 0<M) (hL : ∀ i,M≤L i)
    (P : MvPolynomial (Fin n) (ZMod p)) (hP : P≠0) (hd : P.totalDegree≤d) :
    probability L s P ≤ (2:ℚ≥0)^n*((n:ℚ≥0)*((d:ℚ≥0)/((min M p:ℕ):ℚ≥0))) := by
  rw [pushforward]
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply weighted_degree _ P hP d (min M p) hd (lt_min hM hp)
  · intro i
    rw [axis_card]
    exact min_le_min (hL i) le_rfl
  · intro i z _
    exact atom_dominance (L i) (s i) (hM.trans_le (hL i)) z

end ActualTZSignedGridPushforward318
