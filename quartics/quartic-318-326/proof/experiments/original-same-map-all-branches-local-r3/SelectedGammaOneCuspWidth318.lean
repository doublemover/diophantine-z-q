module
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic
public section
noncomputable section

open scoped MatrixGroups
open CongruenceSubgroup

namespace SelectedGammaOneCuspWidth318

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℤ

private theorem literal_conjugation (a b c d n : ℤ) (hdet : a*d-b*c=1) :
    (!![a,b;c,d] : Mat) * !![1,n;0,1] * !![d,-b;-c,a] =
      !![1-a*c*n,a*a*n;-c*c*n,1+a*c*n] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet

/-- This is the actual integral conjugation of the modular translation,
not a proposed matrix supplied as an input. -/
theorem conjugate_matrix (g : SL(2, ℤ)) (n : ℤ) :
    (↑(g * ModularGroup.T^n * g⁻¹) : Mat) =
      !![1-g 0 0*g 1 0*n, g 0 0*g 0 0*n;
        -(g 1 0)*g 1 0*n, 1+g 0 0*g 1 0*n] := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hinv : (↑(g⁻¹) : Mat) = !![g 1 1, -(g 0 1); -(g 1 0), g 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  calc
    _ = (g : Mat) * !![1,n;0,1] * !![g 1 1, -(g 0 1); -(g 1 0), g 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_T_zpow, hinv]
    _ = (!![g 0 0,g 0 1;g 1 0,g 1 1] : Mat) * !![1,n;0,1] *
        !![g 1 1, -(g 0 1); -(g 1 0), g 0 0] :=
      congrArg (fun A : Mat => A * !![1,n;0,1] * !![g 1 1, -(g 0 1); -(g 1 0), g 0 0])
        (Matrix.eta_fin_two (g : Mat))
    _ = _ := literal_conjugation _ _ _ _ n hdet

/-- The positive-sign translation returns precisely when its exponent
kills the lower-left entry modulo N. No primitivity of that entry
alone is assumed: use the determinant-one Bézout relation. -/
theorem positive_iff (N : ℕ) (g : SL(2, ℤ)) (n : ℤ) :
    g * ModularGroup.T^n * g⁻¹ ∈ Gamma1 N ↔
      (n:ZMod N) * (g 1 0:ZMod N) = 0 := by
  have hm := conjugate_matrix g n
  have h00 : (g * ModularGroup.T^n * g⁻¹) 0 0 = 1-g 0 0*g 1 0*n :=
    congrArg (fun A : Mat => A 0 0) hm
  have h11 : (g * ModularGroup.T^n * g⁻¹) 1 1 = 1+g 0 0*g 1 0*n :=
    congrArg (fun A : Mat => A 1 1) hm
  have h10 : (g * ModularGroup.T^n * g⁻¹) 1 0 = -(g 1 0)*g 1 0*n :=
    congrArg (fun A : Mat => A 1 0) hm
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hdet' := congrArg (fun x : ℤ => (x:ZMod N)) hdet
  push_cast at hdet'
  rw [Gamma1_mem, h00, h11, h10]
  push_cast
  let a : ZMod N := (g 0 0:ℤ)
  let b : ZMod N := (g 0 1:ℤ)
  let c : ZMod N := (g 1 0:ℤ)
  let d : ZMod N := (g 1 1:ℤ)
  let m : ZMod N := n
  change a*d-b*c=1 at hdet'
  change (1-a*c*m=1 ∧ 1+a*c*m=1 ∧ (-c)*c*m=0) ↔ m*c=0
  constructor
  · rintro ⟨ha,_,hc⟩
    have hac : a*c*m=0 := by linear_combination -ha
    have hcc : c*c*m=0 := by linear_combination -hc
    calc
      m*c = (a*d-b*c)*(m*c) := by rw [hdet', one_mul]
      _ = d*(a*c*m)-b*(c*c*m) := by ring
      _ = 0 := by rw [hac,hcc,mul_zero,mul_zero,sub_zero]
  · intro h
    have hac : a*c*m=0 := by rw [show a*c*m=a*(m*c) by ring,h,mul_zero]
    have hcc : c*c*m=0 := by rw [show c*c*m=c*(m*c) by ring,h,mul_zero]
    exact ⟨by rw [hac,sub_zero], by rw [hac,add_zero], by rw [neg_mul,neg_mul,hcc,neg_zero]⟩

/-- No negative translation lies in the actual Gamma1 for N>4.
Both reduced diagonals would be 1 despite total trace −2. -/
theorem no_negative (N : ℕ) (hN : 4 < N) (g : SL(2, ℤ)) (n : ℤ) :
    -(g * ModularGroup.T^n * g⁻¹) ∉ Gamma1 N := by
  intro h
  obtain ⟨h00,h11,_⟩ := (Gamma1_mem N _).mp h
  have hm := conjugate_matrix g n
  have hneg : (↑(-(g * ModularGroup.T^n * g⁻¹)) : Mat) =
      -(!![1-g 0 0*g 1 0*n,g 0 0*g 0 0*n;-(g 1 0)*g 1 0*n,1+g 0 0*g 1 0*n] : Mat) := by
    rw [Matrix.SpecialLinearGroup.coe_neg,hm]
  have he00 : (-(g * ModularGroup.T^n * g⁻¹)) 0 0 = -(1-g 0 0*g 1 0*n) :=
    congrArg (fun A : Mat => A 0 0) hneg
  have he11 : (-(g * ModularGroup.T^n * g⁻¹)) 1 1 = -(1+g 0 0*g 1 0*n) :=
    congrArg (fun A : Mat => A 1 1) hneg
  rw [he00] at h00
  rw [he11] at h11
  push_cast at h00 h11
  have h4 : (4:ZMod N)=0 := by linear_combination -h00-h11
  have hd := (ZMod.natCast_eq_zero_iff 4 N).mp h4
  exact (not_le_of_gt hN) (Nat.le_of_dvd (by decide) hd)

/-- Effective period criterion at the actual cusp g∞. The disjunction
is membership up to the single global sign of the PSL quotient. -/
theorem effective_period (N : ℕ) [NeZero N] (hN : 4 < N) (g : SL(2, ℤ)) (k : ℕ) :
    (g * ModularGroup.T^(k:ℤ) * g⁻¹ ∈ Gamma1 N ∨
      -(g * ModularGroup.T^(k:ℤ) * g⁻¹) ∈ Gamma1 N) ↔
      (N / N.gcd ((g 1 0:ZMod N).val)) ∣ k := by
  let c : ZMod N := (g 1 0:ℤ)
  have hOrder : addOrderOf c = N / N.gcd c.val := by
    calc
      _ = addOrderOf (c.val : ZMod N) := congrArg addOrderOf (ZMod.natCast_zmod_val c).symm
      _ = _ := ZMod.addOrderOf_coe c.val (NeZero.ne N)
  rw [or_iff_left (no_negative N hN g (k:ℤ)), positive_iff]
  change ((k:ℤ):ZMod N)*c=0 ↔ (N/N.gcd c.val) ∣ k
  rw [Int.cast_natCast, ← nsmul_eq_mul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hOrder]

/-- The displayed positive integer is achieved and minimal among actual
effective positive periods. -/
theorem least_positive (N : ℕ) [NeZero N] (hN : 4 < N) (g : SL(2, ℤ)) :
    let w := N/N.gcd ((g 1 0:ZMod N).val)
    0 < w ∧ g * ModularGroup.T^(w:ℤ) * g⁻¹ ∈ Gamma1 N ∧
      ∀ k : ℕ, 0 < k →
        (g * ModularGroup.T^(k:ℤ) * g⁻¹ ∈ Gamma1 N ∨
          -(g * ModularGroup.T^(k:ℤ) * g⁻¹) ∈ Gamma1 N) → w ≤ k := by
  dsimp only
  let c : ZMod N := (g 1 0:ℤ)
  let w := N/N.gcd c.val
  have hOrder : addOrderOf c = w := by
    calc
      _ = addOrderOf (c.val : ZMod N) := congrArg addOrderOf (ZMod.natCast_zmod_val c).symm
      _ = _ := ZMod.addOrderOf_coe c.val (NeZero.ne N)
  have hw : 0 < w := hOrder ▸ addOrderOf_pos c
  have hmem := (effective_period N hN g w).mpr (dvd_refl w)
  exact ⟨hw, hmem.resolve_right (no_negative N hN g (w:ℤ)),
    fun k hk h => Nat.le_of_dvd hk ((effective_period N hN g k).mp h)⟩

end SelectedGammaOneCuspWidth318

#print axioms SelectedGammaOneCuspWidth318.conjugate_matrix
#print axioms SelectedGammaOneCuspWidth318.effective_period
#print axioms SelectedGammaOneCuspWidth318.least_positive
