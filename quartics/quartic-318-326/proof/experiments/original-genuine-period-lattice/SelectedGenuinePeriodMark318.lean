module
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic
public section
noncomputable section

namespace SelectedGenuinePeriodMark318

/-- The actual oriented basis (1,τ), not an auxiliary lattice with
the same discriminant. -/
@[expose] def period (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := (τ : ℂ)
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have hi : b*(τ : ℂ).im = 0 := by
      simpa [Complex.real_smul,Complex.add_im,Complex.mul_im] using congrArg Complex.im h
    have hb := (mul_eq_zero.mp hi).resolve_right τ.im_pos.ne'
    exact ⟨by simpa [hb,Complex.real_smul] using h,hb⟩

@[expose] def liftMark (N : ℕ) : ℂ := 1/(N : ℂ)

abbrev Torus (τ : UpperHalfPlane) := ℂ ⧸ (period τ).lattice.toAddSubgroup

@[expose] def markedTorus (N : ℕ) (τ : UpperHalfPlane) : Torus τ :=
  QuotientAddGroup.mk' (period τ).lattice.toAddSubgroup (liftMark N)

/-- Every multiplication test is at the SAME rational lattice lift.
In particular the proof does not infer exact order by point count. -/
theorem nsmul_mem_lattice_iff (τ : UpperHalfPlane) (N k : ℕ) (hN : N ≠ 0) :
    k • liftMark N ∈ (period τ).lattice ↔ N ∣ k := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hk : k • liftMark N = (k : ℂ)/(N : ℂ) := by
    rw [liftMark,nsmul_eq_mul,mul_one_div]
  rw [hk,PeriodPair.mem_lattice]
  change (∃ m n : ℤ, (m : ℂ)*1+(n : ℂ)*(τ : ℂ) = (k : ℂ)/(N : ℂ)) ↔ N ∣ k
  constructor
  · rintro ⟨m,n,he⟩
    have hi : (n : ℝ)*(τ : ℂ).im = 0 := by
      simpa [Complex.add_im,Complex.mul_im] using congrArg Complex.im he
    have hn' : (n : ℝ) = 0 := (mul_eq_zero.mp hi).resolve_right τ.im_pos.ne'
    have hz : n = 0 := by exact_mod_cast hn'
    have hm : (m : ℂ) = (k : ℂ)/(N : ℂ) := by simpa [hz] using he
    have hmul : (m : ℂ)*(N : ℂ) = (k : ℂ) := (eq_div_iff hn).mp hm
    have hmul' : m*(N : ℤ) = (k : ℤ) := by exact_mod_cast hmul
    have hd : (N : ℤ) ∣ (k : ℤ) := ⟨m,by simpa [mul_comm] using hmul'.symm⟩
    exact_mod_cast hd
  · rintro ⟨t,rfl⟩
    refine ⟨(t : ℤ),0,?_⟩
    simp only [mul_one,Int.cast_zero,zero_mul,add_zero,Nat.cast_mul,Int.cast_natCast]
    field_simp [hn] <;> ring

theorem markedTorus_nsmul_eq_zero_iff (τ : UpperHalfPlane) (N k : ℕ) (hN : N ≠ 0) :
    k • markedTorus N τ = 0 ↔ N ∣ k := by
  unfold markedTorus
  rw [← map_nsmul,QuotientAddGroup.eq_zero_iff]
  exact nsmul_mem_lattice_iff τ N k hN

theorem liftMark_nonperiod (τ : UpperHalfPlane) (N : ℕ) (hN : 1 < N) :
    liftMark N ∉ (period τ).lattice := by
  intro h
  have hd : N ∣ 1 := (nsmul_mem_lattice_iff τ N 1 (by omega)).mp (by simpa using h)
  exact (not_le_of_gt hN) (Nat.le_of_dvd (by decide) hd)

@[expose] def shortA (τ : UpperHalfPlane) : ℂ := -(period τ).g₂/4
@[expose] def shortB (τ : UpperHalfPlane) : ℂ := -(period τ).g₃/4
@[expose] def markX (N : ℕ) (τ : UpperHalfPlane) : ℂ :=
  (period τ).weierstrassP (liftMark N)
@[expose] def markY (N : ℕ) (τ : UpperHalfPlane) : ℂ :=
  (period τ).derivWeierstrassP (liftMark N)/2

/-- Actual Weierstrass lattice sums satisfy the normalized SHORT
equation at the exact lifted mark, finite since it is a nonperiod. -/
theorem marked_short_equation (τ : UpperHalfPlane) (N : ℕ) (hN : 1 < N) :
    markY N τ^2 = markX N τ^3+shortA τ*markX N τ+shortB τ := by
  have h := (period τ).derivWeierstrassP_sq (liftMark N) (liftMark_nonperiod τ N hN)
  dsimp only [shortA,shortB,markX,markY]
  linear_combination h/4

end SelectedGenuinePeriodMark318

#print axioms SelectedGenuinePeriodMark318.nsmul_mem_lattice_iff
#print axioms SelectedGenuinePeriodMark318.markedTorus_nsmul_eq_zero_iff
#print axioms SelectedGenuinePeriodMark318.marked_short_equation
