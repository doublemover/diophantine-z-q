module
public import IntegralOriginalRootCoordinates318
public import IntegralGlobalBicanonicalPair318
public import ContactBicanonicalCoefficients318
public section
noncomputable section
namespace IntegralRationalBranchCoefficients318
open IntegralRationalFiniteAtlas318 IntegralOriginalRootCoordinates318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The signed local parameter is the same original root on each complete
rational branch localization, including at its ramification point. -/
theorem coordinate (i : Fin 4) :
    branchEquiv c i (IntegralBranchCoordinates318.sourceCoordinate ℚ c i) =
      ContactFrameNormalization318.sourceCoordinate c i := by
  rw [IntegralOriginalRootCoordinates318.coordinate_eq_root,branchEquiv_source,
    rational_root,BranchOriginalCoordinate318.coordinate_eq_root]

theorem parameter (i : Fin 4) :
    branchEquiv c i (IntegralBranchCoordinates318.sourceT ℚ c i) =
      ContactBicanonicalCoefficients318.branchT c i := rfl

theorem inverseDenominator (i : Fin 4) :
    branchEquiv c i (IsLocalization.Away.invSelf (IntegralBranchDenominatorCover318.denominator ℚ c i)) =
      IsLocalization.Away.invSelf (SourceDenominatorCover318.denominator c i) := rfl

/-- Exact coefficient comparison, with the factor4 and inverse twist retained. -/
theorem coefficient0 (i : Fin 4) :
    branchEquiv c i (IntegralBranchBicanonical318.coefficient0 ℚ c i) =
      ContactBicanonicalCoefficients318.branchQ0 c i := by
  have ht : IntegralBranchDenominatorCover318.twistUnit ℚ c i =
      SourceDenominatorCover318.twistUnit c i := rfl
  simp only [IntegralBranchBicanonical318.coefficient0,map_mul,map_ofNat,
    AlgEquiv.commutes,inverseDenominator,ht,
    ContactBicanonicalCoefficients318.branchQ0,ContactBicanonicalCoefficients318.branchScale,
    ContactBicanonicalCoefficients318.fourUnit,Units.val_mul,Units.val_mk0,map_mul,map_ofNat]

theorem coefficient1 (i : Fin 4) :
    branchEquiv c i (IntegralBranchBicanonical318.coefficient1 ℚ c i) =
      ContactBicanonicalCoefficients318.branchQ1 c i := by
  rw [IntegralBranchBicanonical318.coefficient1,map_mul,parameter,coefficient0]
  all_goals rfl

/-- Both J-squared coefficients used by the integral global pair map to
precisely J-squared times the original rational bicanonical coefficients. -/
theorem scaled_coefficient (i : Fin 4) (n : Fin 2) :
    branchEquiv c i (IntegralGlobalBicanonicalPair318.branchCoefficient ℚ c i n) =
      (VerticalSection318.J : ContactIntrinsicFrames318.BranchRing c i)^2 *
        (if n=0 then ContactBicanonicalCoefficients318.branchQ0 c i
          else ContactBicanonicalCoefficients318.branchQ1 c i) := by
  by_cases hn : n=0
  · simp only [IntegralGlobalBicanonicalPair318.branchCoefficient,hn,ite_true,
      map_mul,map_pow,map_intCast,coefficient0]
  · simp only [IntegralGlobalBicanonicalPair318.branchCoefficient,hn,ite_false,
      map_mul,map_pow,map_intCast,coefficient1]

theorem differential (i : Fin 4) :
    AlgHomDifferential318.map (branchEquiv c i).toAlgHom
      (KaehlerDifferential.D ℚ (IntegralBranchCoordinates318.B ℚ c i)
        (IntegralBranchCoordinates318.sourceCoordinate ℚ c i)) =
      KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
        (ContactFrameNormalization318.sourceCoordinate c i) := by
  rw [AlgHomDifferential318.map_D,coordinate]
end IntegralRationalBranchCoefficients318
