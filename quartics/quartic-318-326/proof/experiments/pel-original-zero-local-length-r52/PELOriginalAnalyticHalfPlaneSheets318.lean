module
public import PELOriginalGlobalHalfPlaneSheets318
public import ComplexCurveContinuousLift318
public import ComplexSphereAffineAutomorphisms318
public section
noncomputable section
namespace PELOriginalAnalyticHalfPlaneSheets318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalGlobalHalfPlaneSheets318 LegendreHalfPlaneAnalyticSheets318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopologicalAtlas318
open PELOriginalCharacterComplexAtlas318 PELOriginalNormalizedDoubleCover318
open PELOriginalHalfPlaneDoubleCover318 ComplexSphereCharts318
variable (i:Fin 4) (upper:Bool)
local instance : ChartedSpace ℂ (CharacterBase i):=characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- Total representative of a constructed global sheet; only its actual
open halfplane is used analytically. Values outside are irrelevant. -/
@[expose] def totalSheet (e:BaseFiber i upper) (z:ℂ) : CharacterBase i:=
  if hz:z∈domain upper then sheet i upper e ⟨z,hz⟩ else e.val
lemma totalSheet_eq (e:BaseFiber i upper) (z:Half upper) :
    totalSheet i upper e z=sheet i upper e z := by
  simp only [totalSheet,dif_pos z.property]

lemma totalSheet_continuousOn (e:BaseFiber i upper) :
    ContinuousOn (totalSheet i upper e) (domain upper) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he:(domain upper).domRestrict (totalSheet i upper e)=sheet i upper e := by
    funext z
    exact totalSheet_eq i upper e z
  rw [he]
  exact (sheet i upper e).continuous

/-- The SAME globally continuous original sheet is now holomorphic in the
unchanged original character-curve atlas. Both regular and omitted-inertia
points are covered by the proved local-homeomorphism theorem. -/
theorem totalSheet_holomorphic (e:BaseFiber i upper) (z:ℂ) (hz:z∈domain upper) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (totalSheet i upper e) z := by
  have hproj:∀w∈domain upper,normalizedMap i (totalSheet i upper e w)=(w:OnePoint ℂ) := by
    intro w hw
    rw [show totalSheet i upper e w=sheet i upper e ⟨w,hw⟩ from totalSheet_eq i upper e ⟨w,hw⟩]
    exact sheet_projection i upper e ⟨w,hw⟩
  apply ComplexCurveContinuousLift318.lift_at (normalizedMap i)
    ((normalizedMap i) ⁻¹' nonreal) (covering_nonreal i).isLocalHomeomorphOn
    (totalSheet i upper e) ((↑):ℂ→OnePoint ℂ) z
  · change normalizedMap i (totalSheet i upper e z)∈nonreal
    rw [hproj z hz]
    exact ⟨z,domain_nonreal upper z hz,rfl⟩
  · exact PELOriginalNormalizedDoubleCover318.holomorphic i _
  · exact (totalSheet_continuousOn i upper e z hz).continuousAt ((domain_open upper).mem_nhds hz)
  · exact ComplexSphereAffineAutomorphisms318.coe_holomorphic z
  · filter_upwards [(domain_open upper).mem_nhds hz] with w hw
    exact hproj w hw
end PELOriginalAnalyticHalfPlaneSheets318
