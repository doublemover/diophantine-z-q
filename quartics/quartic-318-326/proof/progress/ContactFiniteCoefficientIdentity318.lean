module
public import ContactBranchDifferential318
public import BicanonicalCoefficientIdentity318
public import BranchOverlapLocalization318
public section
noncomputable section
namespace ContactFiniteCoefficientIdentity318
open Polynomial ContactBicanonicalCoefficients318
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The contact quartic, as a function on the entire branch chart. -/
@[expose] def branchP (i : Fin 4) : BranchRing c i :=
  algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i)
    (SourceOpenFractionField318.d c)

lemma branch_factor_product (i : Fin 4) :
    (branchT c i - algebraMap ℚ (BranchRing c i) (LinearContactSquareclass318.contacts i))*
      algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i)
        (SourceDenominatorCover318.denominator c i) =
    algebraMap ℚ (BranchRing c i) (SourceDenominatorCover318.twistUnit c i:ℚ)*branchP c i := by
  have h := congrArg (algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i))
    (BranchOverlapLocalization318.factor_product c i)
  have hC (q : ℚ) : algebraMap ℚ[X] (BranchRing c i) (C q)=
      algebraMap ℚ (BranchRing c i) q :=
    (IsScalarTower.algebraMap_apply ℚ ℚ[X] (BranchRing c i) q).symm
  simpa only [map_mul,BranchOverlapLocalization318.factor,map_sub,
    ←IsScalarTower.algebraMap_apply,hC,branchT,branchP] using h

lemma branchScale_map (i : Fin 4) :
    algebraMap ℚ (BranchRing c i) (branchScale c i:ℚ) =
      4 * algebraMap ℚ (BranchRing c i) (SourceDenominatorCover318.twistUnit c i:ℚ) *
        algebraMap ℚ (BranchRing c i) (↑(c i)⁻¹:ℚ) := by
  simp only [branchScale,fourUnit,Units.val_mul,Units.val_mk0,map_mul,map_ofNat]

/-- Exact cleared bicanonical identity at every finite branch point.
Only the other three branch factors were inverted. -/
theorem finite_cleared (i : Fin 4) :
    branchP c i * branchQ0 c i =
      (2 * algebraMap ℚ (BranchRing c i) (↑(c i)⁻¹:ℚ) *
        ContactFrameNormalization318.sourceCoordinate c i)^2 := by
  rw [branchQ0,branchScale_map]
  exact BicanonicalCoefficientIdentity318.finite_cleared _ _ _ _ _ _ _ _
    (branch_factor_product c i)
    (IsLocalization.Away.mul_invSelf (SourceDenominatorCover318.denominator c i))
    (ContactBranchCoordinate318.coordinate_square c i)

/-- The cleared coefficient is the square of the actual differential-frame
value of Dt, not a guessed rational differential scale. -/
theorem finite_cleared_frame (i : Fin 4) :
    branchP c i * branchQ0 c i =
      (ContactDifferentialFrames318.sourceLocalizationFrame c i
        (KaehlerDifferential.D ℚ (BranchRing c i) (branchT c i)))^2 := by
  rw [ContactBranchDifferential318.frame_D_branchT]
  exact finite_cleared c i
end ContactFiniteCoefficientIdentity318
