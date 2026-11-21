module
public import OriginalInteriorTelescoping318
public import ActualPointedCyclicPairing318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayPointedAnchor318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualPointedCyclicPairing318

@[expose] def shiftAt (r : Row) (j : ℕ) (m : Fin r.M) : ℤ :=
  shift r j ((m.val:ℤ)+1)

def primeAt (r : Row) (j : ℕ) (x : Fin r.n) : ℝ :=
  let y := rep r.n ((x.val:ℤ)+1)
  if (r.cut:ℤ)≤y then r.phiRatio*logPrimeRay r.ray ((r.W:ℤ)*y+residue r j) else 0

def meanAt (r : Row) (j : ℕ) (x : Fin r.n) : ℝ :=
  r.mu ((r.W:ℤ)*rep r.n ((x.val:ℤ)+1)+residue r j)

def center (r : Row) (j : ℕ) (x : Fin r.n) : ℝ :=
  centeredAt r j ((x.val:ℤ)+1)

theorem center_eq (r : Row) (j : ℕ) (x : Fin r.n) :
    center r j x=primeAt r j x-meanAt r j x := by
  simp only [center,centeredAt,primeAt,meanAt]

/-- Preserve the actual interior dummy and precisely the old prefix
j factors, evaluated at the exact inverse cyclic translation. -/
def test (r : Row) (hn : 0<r.n) (j : ℕ) (y : Fin r.n) : ℝ :=
  ∑ m : Fin r.M,
    let z : Dom r := (move hn (-shiftAt r j m) y,m)
    dummy r z * (∏ i∈(Finset.range r.k).erase j, if i<j then f r i z else mean r i z)

def correlation (r : Row) (hn : 0<r.n) (j : ℕ) (g : Fin r.n → ℝ) : ℝ :=
  ∑ y : Fin r.n, g y * test r hn j y

theorem center_at_shift (r : Row) (hn : 0<r.n) (j : ℕ) (z : Dom r) :
    center r j (move hn (shiftAt r j z.2) z.1)=f r j z-mean r j z := by
  have hrep : rep r.n (((move hn (shiftAt r j z.2) z.1).val:ℤ)+1)=arg r j z := by
    simp only [rep,arg,shiftAt,move_val,add_sub_cancel_right,Int.emod_emod]
    have h : (z.1.val:ℤ)+1+shift r j ((z.2.val:ℤ)+1)-1 =
        (z.1.val:ℤ)+shift r j ((z.2.val:ℤ)+1) := by ring
    rw [h]
  change (let y := rep r.n (((move hn (shiftAt r j z.2) z.1).val:ℤ)+1)
          let p := (r.W:ℤ)*y+residue r j
          (if (r.cut:ℤ)≤y then r.phiRatio*logPrimeRay r.ray p else 0)-r.mu p)=_
  dsimp only
  rw [hrep] <;> rfl

theorem exact_pointed_pairing (r : Row) (hn : 0<r.n) (j : ℕ) :
    mass r (fun z => (f r j z-mean r j z) *
      ∏ i∈(Finset.range r.k).erase j, if i<j then f r i z else mean r i z) =
        correlation r hn j (center r j) := by
  let C (z : Dom r) := dummy r z *
    (∏ i∈(Finset.range r.k).erase j, if i<j then f r i z else mean r i z)
  calc
    _ = ∑ z : Dom r, center r j
        (translation hn (shiftAt r j z.2) z.1) * C z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [translation_apply,center_at_shift]
      unfold C
      ring
    _ = _ := by
      simpa only [correlation,test,C,translation_symm_apply] using
        anchored_pairing (fun m : Fin r.M => translation hn (shiftAt r j m)) (center r j) C

/-- One bound per actual distinguished prime. No arbitrary family of
nilsequences, cofactors, or polynomial tuples is demanded here. -/
def AnchorBudget (r : Row) (hn : 0<r.n) (eps : ℝ) : Prop :=
  ∀ j<r.k, |correlation r hn j (center r j)|≤eps*((r.n:ℝ)*(r.M:ℝ))

theorem mixed_of_anchor (r : Row) (hn : 0<r.n) (eps : ℝ)
    (h : AnchorBudget r hn eps) : MixedBudget r (eps*((r.n:ℝ)*(r.M:ℝ))) := by
  intro j hj
  rw [exact_pointed_pairing r hn j]
  exact h j hj

/-- Native dense-model bookkeeping, not a density or correlation
theorem. One model occupies the distinguished slot; its VERY SAME
actual test multiplies both the comparison and the modeled center. -/
theorem split_at_model (r : Row) (hn : 0<r.n) (j : ℕ) (g : Fin r.n → ℝ) :
    correlation r hn j (center r j) =
      correlation r hn j (fun x => primeAt r j x-g x) +
      correlation r hn j (fun x => g x-meanAt r j x) := by
  unfold correlation
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [center_eq]
  ring

theorem mixed_of_model_comparisons (r : Row) (hn : 0<r.n) (e₁ e₂ : ℝ)
    (h : ∀ j<r.k, ∃ g : Fin r.n → ℝ,
      |correlation r hn j (fun x => primeAt r j x-g x)| ≤ e₁*((r.n:ℝ)*(r.M:ℝ)) ∧
      |correlation r hn j (fun x => g x-meanAt r j x)| ≤ e₂*((r.n:ℝ)*(r.M:ℝ))) :
    MixedBudget r ((e₁+e₂)*((r.n:ℝ)*(r.M:ℝ))) := by
  apply mixed_of_anchor
  intro j hj
  obtain ⟨g,h₁,h₂⟩ := h j hj
  rw [split_at_model r hn j g]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ e₁*((r.n:ℝ)*(r.M:ℝ))+e₂*((r.n:ℝ)*(r.M:ℝ)) := add_le_add h₁ h₂
    _ = _ := by ring

/-- The exact aggregate signed defect of a row, not a sum of
absolute values. Each old blend_step is invoked once. -/
theorem row_difference (r : Row) (hn : 0<r.n) :
    mass r (fun z => ∏ i∈Finset.range r.k, f r i z) -
      mass r (fun z => ∏ i∈Finset.range r.k, mean r i z) =
      ∑ j∈Finset.range r.k, correlation r hn j (center r j) := by
  let B (j : ℕ) := mass r (blend (f r) (mean r) r.k j)
  have step (j : ℕ) (hj : j<r.k) :
      B (j+1)-B j=correlation r hn j (center r j) := by
    rw [←exact_pointed_pairing r hn j]
    dsimp [B,mass]
    rw [←Finset.sum_sub_distrib]
    simp only [←mul_sub,blend_step _ _ hj]
  have hpartial (j : ℕ) (hj : j≤r.k) :
      B j-B 0=∑ i∈Finset.range j, correlation r hn i (center r i) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hlt : j<r.k := by omega
      rw [Finset.sum_range_succ,←ih hlt.le,←step j hlt]
      ring
  have hlast : B r.k=mass r (fun z => ∏ i∈Finset.range r.k, f r i z) := by
    unfold B blend
    apply congrArg (mass r)
    funext z
    apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hfirst : B 0=mass r (fun z => ∏ i∈Finset.range r.k, mean r i z) := by
    change mass r (blend (f r) (mean r) r.k 0) = _
    apply congrArg (mass r)
    funext z
    simp only [blend,Nat.not_lt_zero,ite_false]
  simpa only [hfirst,hlast] using hpartial r.k le_rfl

/-- A strictly weaker analytic conclusion suffices if only LOWER
mass is required: the total signed defect need not be small above. -/
theorem lower_of_signed_row (r : Row) (hn : 0<r.n) (E : ℝ)
    (h : -E≤∑ j∈Finset.range r.k, correlation r hn j (center r j)) :
    mass r (fun z => ∏ i∈Finset.range r.k, mean r i z) - E ≤
      mass r (fun z => ∏ i∈Finset.range r.k, f r i z) := by
  rw [←row_difference r hn] at h
  linarith only [h]

theorem lower_of_one_sided_anchors (r : Row) (hn : 0<r.n) (E : ℝ)
    (h : ∀ j<r.k, -E≤correlation r hn j (center r j)) :
    mass r (fun z => ∏ i∈Finset.range r.k, mean r i z) - (r.k:ℝ)*E ≤
      mass r (fun z => ∏ i∈Finset.range r.k, f r i z) := by
  apply lower_of_signed_row r hn
  calc
    -((r.k:ℝ)*E)=∑ _j∈Finset.range r.k, -E := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)

end ActualRayPointedAnchor318
