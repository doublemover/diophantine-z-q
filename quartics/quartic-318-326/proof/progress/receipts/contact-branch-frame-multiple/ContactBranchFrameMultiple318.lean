module
public import FrameUnitMultiple318
public import ContactFrameNormalization318
public import ContactIntrinsicFrames318
public section
noncomputable section
namespace ContactBranchFrameMultiple318
open AlgebraicGeometry
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ) (i:Fin 4)
abbrev B:=ContactIntrinsicFrames318.BranchRing c i
abbrev t:B c i:=ContactFrameNormalization318.sourceCoordinate c i
/-- An actual whole-branch factorization is a regular multiple of a local
form with the specified unit-times-coordinate frame coefficient. The twists
remain abstract and every original ring, frame and derivative is retained. -/
@[expose] def of_factorization (ω ω₀:KaehlerDifferential ℚ (B c i)) (k:B c i)
    (hk:IsUnit k) (h:∃a:B c i,ω=(t c i*a) • KaehlerDifferential.D ℚ (B c i) (t c i))
    (h₀:ContactDifferentialFrames318.sourceLocalizationFrame c i ω₀=k*t c i):=
  FrameUnitMultiple318.of_factorization (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (t c i) k ω ω₀ (KaehlerDifferential.D ℚ (B c i) (t c i)) hk
    (ContactFrameNormalization318.source_coordinate_normalized c i) h h₀
end ContactBranchFrameMultiple318
