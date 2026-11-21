module
public import ActualRayPointedAnchor318
public import ActualTZFirstPETEdgeRows318
import all ActualRayPointedAnchor318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualTZOriginalMixedProductRestore318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualPointedCyclicPairing318
open ActualRayPointedAnchor318 ActualTZFirstPETEdgeRows318

def interior (r : Row) (x : Fin r.n) : ℝ :=
  if 5*r.n ≤ 8*(x.val+1) ∧ 4*(x.val+1) ≤ 3*r.n then 1 else 0

def physical (r : Row) (j i : ℕ) (z : Dom r) : ℝ :=
  if i = j then f r j z - mean r j z else if i < j then f r i z else mean r i z

/-- The dummy is not normalized, and only the k genuine factors
are divided by K. The marked function is exactly K⁻¹ times center. -/
def lifted (r : Row) (j : Fin r.k) (K : ℝ) : Nodes r → Fin r.n → ℝ
  | none, x => interior r x
  | some i, x => K⁻¹ * (if i.val = j.val then center r j.val x else
      if i.val < j.val then primeAt r i.val x else meanAt r i.val x)

theorem lifted_mark (r : Row) (j : Fin r.k) (K : ℝ) :
    lifted r j K (some j) = (fun x => K⁻¹ * center r j.val x) := by
  funext x
  simp only [lifted,ite_true]

theorem shifted_mean (r : Row) (hn : 0 < r.n) (i : ℕ) (z : Dom r) :
    meanAt r i (move hn (shiftAt r i z.2) z.1) = mean r i z := by
  have h : rep r.n (((move hn (shiftAt r i z.2) z.1).val : ℤ)+1)=arg r i z := by
    simp only [rep,arg,shiftAt,move_val,add_sub_cancel_right,Int.emod_emod]
    rw [show (z.1.val:ℤ)+1+shift r i ((z.2.val:ℤ)+1)-1 =
      (z.1.val:ℤ)+shift r i ((z.2.val:ℤ)+1) by ring]
  simp only [meanAt,mean,val,h]

theorem shifted_prime (r : Row) (hn : 0 < r.n) (i : ℕ) (z : Dom r) :
    primeAt r i (move hn (shiftAt r i z.2) z.1) = f r i z := by
  have h := center_at_shift r hn i z
  rw [center_eq,shifted_mean] at h
  linarith only [h]

theorem physical_product (r : Row) (j : Fin r.k) (z : Dom r) :
    (∏ i : Fin r.k, physical r j.val i.val z) =
      (f r j.val z - mean r j.val z) *
        ∏ i ∈ (Finset.range r.k).erase j.val, if i < j.val then f r i z else mean r i z := by
  classical
  rw [Fin.prod_univ_eq_prod_range (fun i => physical r j.val i z) r.k]
  rw [←Finset.mul_prod_erase (Finset.range r.k) _ (Finset.mem_range.mpr j.isLt)]
  rw [show physical r j.val j.val z = f r j.val z - mean r j.val z by simp only [physical,ite_true]]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [physical,if_neg (Finset.mem_erase.mp hi).1]

theorem restored_point (r : Row) (hn : 0 < r.n) (j : Fin r.k) (K : ℝ) (z : Dom r) :
    (∏ i : Nodes r, lifted r j K i (move hn (PAt r ((z.2.val:ℤ)+1) i) z.1)) =
      K⁻¹ ^ r.k * (dummy r z *
        ((f r j.val z - mean r j.val z) *
          ∏ i ∈ (Finset.range r.k).erase j.val, if i < j.val then f r i z else mean r i z)) := by
  classical
  rw [Fintype.prod_option]
  have h0 : lifted r j K none (move hn (PAt r ((z.2.val:ℤ)+1) none) z.1) = dummy r z := by
    simp only [PAt,move_zero,lifted,interior,dummy]
  rw [h0]
  have hprod : (∏ i : Fin r.k, lifted r j K (some i)
        (move hn (PAt r ((z.2.val:ℤ)+1) (some i)) z.1)) =
      ∏ i : Fin r.k, K⁻¹ * physical r j.val i.val z := by
    apply Finset.prod_congr rfl
    intro i _
    have hs : PAt r ((z.2.val:ℤ)+1) (some i) = shiftAt r i.val z.2 := by rfl
    rw [hs]
    by_cases hij : i.val = j.val
    · have hEq : i = j := Fin.ext hij
      subst i
      simp only [lifted_mark,center_at_shift,physical,ite_true]
    · simp only [lifted,physical,if_neg hij,shifted_prime r hn i.val z,shifted_mean r hn i.val z]
  rw [hprod,Finset.prod_mul_distrib,physical_product]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

end ActualTZOriginalMixedProductRestore318
