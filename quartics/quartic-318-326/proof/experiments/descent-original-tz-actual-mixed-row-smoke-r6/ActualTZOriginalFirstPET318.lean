module
public import ActualTZFirstPETCopy318
import all ActualTZFirstPETCopy318
public import OriginalInteriorTelescoping318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualTZOriginalFirstPET318
open scoped BigOperators
open ActualTZFirstPETCopy318 OriginalInteriorTelescoping318

/-- Exact historic quadratic, including its old residue remainder.
The ordinary dummy uses the zero table, with residue 1. -/
def input (r : Row) (i : ℕ) : Table (Fin 0) where
  top := d r i*(r.W:ℤ)
  pureSlope := 2*d r i*r.c
  mixed := fun _=>0
  constTerm := (r.b+d r i*r.c^2-residue r i)/(r.W:ℤ)
  fineLin := fun _=>0
  fineQuad := fun _ _=>0

theorem input_exact (r : Row) (i : ℕ) (m : ℤ) (h : Fin 0→ℤ) :
    eval (input r i) m h=shift r i m := by
  simp only [eval,input,shift,zero_mul,Finset.sum_const_zero,add_zero]

private theorem residue_range (r : Row) (i : ℕ) (hW : 0<r.W) :
    1≤residue r i ∧ residue r i≤(r.W:ℤ) := by
  have hWp : (0:ℤ)<r.W := by exact_mod_cast hW
  unfold residue
  have hn := Int.emod_nonneg (r.b+d r i*r.c^2-1) hWp.ne'
  have hu := Int.emod_lt_of_pos (r.b+d r i*r.c^2-1) hWp
  omega

theorem initial_bound (r : Row) (i : ℕ) (D : ℤ) (hD : 0≤D) (hd : |d r i|≤D)
    (hW : 0<r.W) (hb : 1≤r.b ∧ r.b≤(r.W:ℤ)) (hc : 0≤r.c ∧ r.c<(r.W:ℤ)) :
    Bound (input r i) ((2*(D+1))*(r.W:ℤ)) := by
  let W := (r.W:ℤ)
  have hWp : 0<W := by
    change (0:ℤ) < (r.W:ℤ)
    exact_mod_cast hW
  have hWn : 0≤W := hWp.le
  let B := (2*(D+1))*W
  have hB : 0≤B := by unfold B; positivity
  have ht : |d r i*W|≤B := by
    rw [abs_mul,abs_of_nonneg hWn]
    exact (mul_le_mul_of_nonneg_right hd hWn).trans
      (mul_le_mul_of_nonneg_right (by omega : D≤2*(D+1)) hWn)
  have hL : |2*d r i*r.c|≤B := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℤ)≤2),abs_of_nonneg hc.1]
    have hOne : 0≤2*D := by positivity
    have hC : r.c≤W := hc.2.le
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℤ)≤2)) hC hc.1 hOne
    exact h.trans (mul_le_mul_of_nonneg_right (by omega : 2*D≤2*(D+1)) hWn)
  have hRes := residue_range r i hW
  have hDiff : |r.b-residue r i|≤W := by
    apply abs_le.mpr
    constructor <;> change _ ≤ _ <;> omega
  have hSq := pow_le_pow_left₀ hc.1 hc.2.le 2
  have hQ : |d r i*r.c^2|≤D*W^2 := by
    rw [abs_mul (d r i) (r.c^2),abs_of_nonneg (sq_nonneg r.c)]
    exact mul_le_mul hd hSq (sq_nonneg _) hD
  let U := r.b+d r i*r.c^2-residue r i
  have hU : |U|≤B*W := by
    calc
      _ = |(r.b-residue r i)+d r i*r.c^2| := by unfold U; congr 1 <;> ring
      _ ≤ |r.b-residue r i|+|d r i*r.c^2| := abs_add_le _ _
      _ ≤ W+D*W^2 := add_le_add hDiff hQ
      _ ≤ B*W := by
        have h₁ : 1≤W := by omega
        have h₂ := mul_le_mul_of_nonneg_right h₁ hWn
        have h₃ : 0≤D*W^2 := mul_nonneg hD (sq_nonneg _)
        unfold B
        nlinarith only [h₂,h₃,sq_nonneg W]
  have hC : |U/W|≤B := by
    obtain ⟨hl,hu⟩ := abs_le.mp hU
    apply abs_le.mpr
    constructor
    · exact (Int.le_ediv_iff_mul_le hWp).2 (by rw [neg_mul]; exact hl)
    · apply (Int.le_iff_lt_add_one).2
      apply (Int.ediv_lt_iff_lt_mul hWp).2
      calc
        _ ≤ B*W := hu
        _ < (B+1)*W := by rw [add_mul,one_mul]; exact lt_add_of_pos_right _ hWp
  exact ⟨hB,ht,hL,(fun j=>Fin.elim0 j),hC,(fun j=>Fin.elim0 j),(fun j=>Fin.elim0 j)⟩

theorem first_copy_exact (r : Row) (i pivot : ℕ) (e : Bool) (m : ℤ) (h : Fin 0⊕Bool→ℤ) :
    eval (copy (sub (input r i) (input r pivot)) e) m h =
      shift r i (m+h (.inr e))-shift r pivot (m+h (.inr e)) := by
  rw [eval_copy,eval_sub,input_exact,input_exact]

end ActualTZOriginalFirstPET318
