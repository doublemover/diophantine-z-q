module
public import ContactBranchCoordinate318
public import SquareCoordinateDifferential318
public section
noncomputable section
namespace ContactBranchDifferential318
open ContactBicanonicalCoefficients318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- Differentiation of the checked whole-chart square equation. -/
theorem D_branchT (i : Fin 4) :
    KaehlerDifferential.D ℚ (BranchRing c i) (branchT c i) =
      (2 * algebraMap ℚ (BranchRing c i) (↑(c i)⁻¹:ℚ) *
        ContactFrameNormalization318.sourceCoordinate c i) •
          KaehlerDifferential.D ℚ (BranchRing c i)
            (ContactFrameNormalization318.sourceCoordinate c i) :=
  SquareCoordinateDifferential318.D_of_square (R:=ℚ) (S:=BranchRing c i)
    (branchT c i) (ContactFrameNormalization318.sourceCoordinate c i)
    (LinearContactSquareclass318.contacts i) (↑(c i)⁻¹:ℚ)
    (ContactBranchCoordinate318.coordinate_square c i)

/-- The actual finite-chart differential frame retains the full scalar
2*z_i/c_i in the derivative of the contact parameter. -/
theorem frame_D_branchT (i : Fin 4) :
    ContactDifferentialFrames318.sourceLocalizationFrame c i
      (KaehlerDifferential.D ℚ (BranchRing c i) (branchT c i)) =
      2 * algebraMap ℚ (BranchRing c i) (↑(c i)⁻¹:ℚ) *
        ContactFrameNormalization318.sourceCoordinate c i :=
  SquareCoordinateDifferential318.frame_D_of_square (R:=ℚ) (S:=BranchRing c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (branchT c i) (ContactFrameNormalization318.sourceCoordinate c i)
    (LinearContactSquareclass318.contacts i) (↑(c i)⁻¹:ℚ)
    (ContactBranchCoordinate318.coordinate_square c i)
    (ContactFrameNormalization318.source_coordinate_normalized c i)
end ContactBranchDifferential318
