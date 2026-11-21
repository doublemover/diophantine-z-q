module
public import ActualTZOriginalMixedProductRestore318
public import ActualTZPETCoarseEdge318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualTZOriginalMixedRowRestore318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualPointedCyclicPairing318 ActualTZFirstPETEdgeRows318
open ActualTZOriginalMixedProductRestore318

def normalized (r : Row) (hn : 0 < r.n) (j : Fin r.k) (K : ℝ) : ℝ :=
  (∑ x : Fin r.n, ActualTZPETCoarseEdge318.mean r.M 0 (fun m =>
      ∏ i : Nodes r, lifted r j K i (move hn (PAt r (m:ℤ) i) x))) / (r.n:ℝ)

def mixedMass (r : Row) (j : ℕ) : ℝ :=
  mass r (fun z => (f r j z - mean r j z) *
    ∏ i ∈ (Finset.range r.k).erase j, if i < j then f r i z else mean r i z)

theorem exact_scale (r : Row) (hn : 0 < r.n) (j : Fin r.k) (K : ℝ) :
    normalized r hn j K =
      (K⁻¹ ^ r.k * mixedMass r j.val) / ((r.n:ℝ)*(r.M:ℝ)) := by
  classical
  let G (z : Dom r) : ℝ := (f r j.val z - mean r j.val z) *
    ∏ i ∈ (Finset.range r.k).erase j.val, if i < j.val then f r i z else mean r i z
  have hm (x : Fin r.n) :
      ActualTZPETCoarseEdge318.mean r.M 0 (fun m =>
        ∏ i : Nodes r, lifted r j K i (move hn (PAt r (m:ℤ) i) x)) =
      (∑ m : Fin r.M, K⁻¹ ^ r.k * (dummy r (x,m) * G (x,m))) / (r.M:ℝ) := by
    unfold ActualTZPETCoarseEdge318.mean ActualTZPETCoarseEdge318.interval
    simp only [zero_add]
    congr 1
    let P (m : ℕ) : ℝ := ∏ i : Nodes r,
      lifted r j K i (move hn (PAt r ((m+1:ℕ):ℤ) i) x)
    change (∑ m ∈ Finset.range r.M, P m) = _
    rw [←Fin.sum_univ_eq_sum_range P r.M]
    apply Finset.sum_congr rfl
    intro m _
    simp only [P,Nat.cast_add,Nat.cast_one]
    exact restored_point r hn j K (x,m)
  unfold normalized
  simp only [hm,←Finset.sum_div,div_div,←Finset.mul_sum]
  rw [mul_comm (r.M:ℝ) (r.n:ℝ)]
  congr 1
  unfold mixedMass mass
  simp only [Fintype.sum_prod_type,G]

theorem of_normalized (r : Row) (hn : 0 < r.n) (hL : 0 < r.M) (K ζ : ℝ)
    (hK : 0 < K) (h : ∀ j : Fin r.k, |normalized r hn j K| ≤ ζ) :
    MixedBudget r (K^r.k * ζ * ((r.n:ℝ)*(r.M:ℝ))) := by
  intro j hj
  let i : Fin r.k := ⟨j,hj⟩
  have he := h i
  rw [exact_scale] at he
  have hden : 0 < ((r.n:ℝ)*(r.M:ℝ)) := by positivity
  have hPow : 0 < K^r.k := pow_pos hK _
  have hInv : 0 < K⁻¹ ^ r.k := pow_pos (inv_pos.mpr hK) _
  rw [abs_div,abs_of_pos hden,abs_mul,abs_of_pos hInv,inv_pow] at he
  have h' := (div_le_iff₀ hden).1 he
  rw [←div_eq_inv_mul] at h'
  have h'' := (div_le_iff₀ hPow).1 h'
  change |mixedMass r i.val| ≤ _
  exact h''.trans_eq (by ring)

end ActualTZOriginalMixedRowRestore318
