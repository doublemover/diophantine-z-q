module
public import ContactFrameNormalization318
public section
noncomputable section
namespace ContactBicanonicalCoefficients318
open Polynomial
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev BranchRing (i : Fin 4) := Localization.Away (SourceDenominatorCover318.denominator c i)
@[expose] def fourUnit : ℚˣ := Units.mk0 4 (by norm_num)
@[expose] def branchScale (i : Fin 4) : ℚˣ :=
  fourUnit * SourceDenominatorCover318.twistUnit c i * (c i)⁻¹
@[expose] def branchQ0 (i : Fin 4) : BranchRing c i :=
  algebraMap ℚ (BranchRing c i) (branchScale c i : ℚ) *
    IsLocalization.Away.invSelf (SourceDenominatorCover318.denominator c i)
@[expose] def branchT (i : Fin 4) : BranchRing c i :=
  algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i)
    (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) X)
@[expose] def branchQ1 (i : Fin 4) : BranchRing c i := branchT c i * branchQ0 c i

/-- This concerns the actual inverted branch denominator, not generic-point coefficients. -/
theorem branchQ0_unit (i : Fin 4) : IsUnit (branchQ0 c i) := by
  apply IsUnit.mul ((branchScale c i).isUnit.map (algebraMap ℚ (BranchRing c i)))
  apply isUnit_iff_exists_inv.mpr
  refine ⟨algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i)
    (SourceDenominatorCover318.denominator c i),?_⟩
  rw [mul_comm,IsLocalization.Away.mul_invSelf]

@[expose] def infinityTwist : ℚˣ := ∏ j : Fin 3, c j.succ
@[expose] def infinityScale (n : ℕ) : ℚˣ := fourUnit * infinityTwist c * ((c 0)⁻¹)^n
@[expose] def infinityDenominatorInverse : InfinityGlobalChart318.InfinityOrder c :=
  algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c)
    (IsLocalization.Away.invSelf (InfinityOpenChart318.denominator c))

/-- Actual u=c_0/y_0 convention, with coefficient 4*C_0*u^2/(c_0^5*D_inf). -/
@[expose] def infinityQ0 : InfinityGlobalChart318.InfinityOrder c :=
  algebraMap ℚ (InfinityGlobalChart318.InfinityOrder c) (infinityScale c 5 : ℚ) *
    (ContactFrameNormalization318.infinityCoordinate c)^2 * infinityDenominatorInverse c
/-- Actual coefficient 4*C_0/(c_0^4*D_inf). -/
@[expose] def infinityQ1 : InfinityGlobalChart318.InfinityOrder c :=
  algebraMap ℚ (InfinityGlobalChart318.InfinityOrder c) (infinityScale c 4 : ℚ) *
    infinityDenominatorInverse c

theorem infinityDenominatorInverse_unit : IsUnit (infinityDenominatorInverse c) := by
  have h : IsUnit (IsLocalization.Away.invSelf (S:=InfinityOpenChart318.OpenBase c)
      (InfinityOpenChart318.denominator c)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c)
      (InfinityOpenChart318.denominator c),?_⟩
    rw [mul_comm,IsLocalization.Away.mul_invSelf]
  exact h.map (algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c))

theorem infinityQ1_unit : IsUnit (infinityQ1 c) :=
  ((infinityScale c 4).isUnit.map (algebraMap ℚ (InfinityGlobalChart318.InfinityOrder c))).mul
    (infinityDenominatorInverse_unit c)
end ContactBicanonicalCoefficients318
