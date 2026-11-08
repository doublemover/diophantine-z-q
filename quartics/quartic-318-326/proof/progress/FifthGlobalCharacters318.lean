module
public import FifthSignRestriction318
public import ContactGlobalSectionDetection318
public section
noncomputable section
namespace FifthGlobalCharacters318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthOpenSigns318 FifthSignRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Transfer an exact whole-open differential eigenrelation to the actual
canonical global source-sign pullback, using proved global detection. -/
theorem global_of_affine (b:Fin 4→Bool) (s:Γ(M,⊤)) (ω:KaehlerDifferential ℚ O)
    (hs:IntrinsicChartSections318.sectionMap j p (ContactOverlapIntrinsic318.over_Q units) ω=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)
    (hw:AlgHomDifferential318.map (sign b) ω=algebraMap ℚ O (epsilon b) • ω):
    ContactDifferentialCharacters318.action b s=
      ContactCharacterGlobalIndependence318.constants (epsilon b) • s:=by
  apply ContactGlobalSectionDetection318.restrict_injective units
  rw [Scheme.Modules.map_smul,FifthGlobalIndependence318.constants_restrict]
  have h1:=restrict_action b s ω hs
  have h2:=congrArg (IntrinsicChartSections318.sectionMap j p
    (ContactOverlapIntrinsic318.over_Q units)) hw
  have h3:=IntrinsicChartSections318.section_smul j p (ContactOverlapIntrinsic318.over_Q units)
    (algebraMap ℚ O (epsilon b)) ω
  exact h1.trans (h2.trans (h3.trans (congrArg
    (fun v:Γ(M,j ''ᵁ ⊤)=>ScaledGlobalSectionRestriction318.scalar j
      (algebraMap ℚ O (epsilon b)) • v) hs)))

/-- Full-root character of the genuine fifth globally glued regular form. -/
theorem glued_eigenrelation (b:Fin 4→Bool):
    ContactDifferentialCharacters318.action b FifthGlobalDifferential318.differential=
      ContactCharacterGlobalIndependence318.constants (epsilon b) • FifthGlobalDifferential318.differential:=
  global_of_affine b _ _ FifthGlobalIndependence318.restrict.symm (FifthAffineCharacter318.glued_form b)

/-- Full-root character of the actual fifth completed-map invariant pullback,
with its previously fixed -41160 normalization unchanged. -/
theorem actual_eigenrelation (b:Fin 4→Bool):
    ContactDifferentialCharacters318.action b FifthActualDifferential318.differential=
      ContactCharacterGlobalIndependence318.constants (epsilon b) • FifthActualDifferential318.differential:=
  global_of_affine b _ _ FifthActualDifferentialRestriction318.restrict (FifthAffineCharacter318.actual_form b)
end FifthGlobalCharacters318
