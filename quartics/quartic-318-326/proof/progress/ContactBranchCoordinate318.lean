module
public import ContactBicanonicalCoefficients318
public section
noncomputable section
namespace ContactBranchCoordinate318
open Polynomial
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

lemma branchCoordinate_eq_root (i : Fin 4) :
    ContactFrameNormalization318.branchCoordinate c i =
      AdjoinRoot.root (QuadraticPresentation318.polynomial
        (LinearRootCoordinate318.parameter (c i) (LinearContactSquareclass318.contacts i))) :=
  LinearRootCoordinate318.inverse_X (c i) (LinearContactSquareclass318.contacts i)

/-- The normalized differential coordinate is the actual ramified square
coordinate on the entire finite branch chart, not merely at its generic point. -/
theorem coordinate_square (i : Fin 4) :
    ContactBicanonicalCoefficients318.branchT c i -
      algebraMap ℚ (ContactBicanonicalCoefficients318.BranchRing c i)
        (LinearContactSquareclass318.contacts i) =
    algebraMap ℚ (ContactBicanonicalCoefficients318.BranchRing c i) (↑(c i)⁻¹:ℚ) *
      (ContactFrameNormalization318.sourceCoordinate c i)^2 := by
  apply (SourceBranchLocalization318.sourceLocalizationEquiv c i).injective
  rw [map_sub,map_mul,map_pow,AlgEquiv.commutes,AlgEquiv.commutes]
  rw [ContactFrameNormalization318.sourceCoordinate,AlgEquiv.apply_symm_apply]
  rw [ContactBicanonicalCoefficients318.branchT,
    SourceBranchLocalization318.sourceLocalizationEquiv_on_source,
    SourceBranchLocalization318.sourceMap_on_polynomial]
  have h := congrArg
    (algebraMap (SourceFiniteBranch318.OpenBase c i) (SourceFiniteBranch318.OpenOrder c i))
    (SourceFiniteBranch318.source_contact_square c i)
  have hC (q : ℚ) :
      algebraMap ℚ[X] (SourceFiniteBranch318.OpenOrder c i) (C q)=
        algebraMap ℚ (SourceFiniteBranch318.OpenOrder c i) q :=
    (IsScalarTower.algebraMap_apply ℚ ℚ[X] (SourceFiniteBranch318.OpenOrder c i) q).symm
  simpa only [map_sub,map_mul,map_pow,ContactFrameNormalization318.branchOrderCoordinate,
    branchCoordinate_eq_root,FiniteBranchChart318.openRoot,
    ←IsScalarTower.algebraMap_apply,hC] using h
end ContactBranchCoordinate318
