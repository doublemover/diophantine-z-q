module
public import PELArithmeticOriginalFibers318
public section
noncomputable section
namespace PELJointHolomorphicLift318
open QuaternionicRealPeriod318 QuaternionicUnitPeriodTransport318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELHolomorphicFamilyProjection318 PELOriginalHolomorphicFibers318
open PELJointArithmeticLift318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
variable (f : Total → Total) (lift : Cover → Cover) (F : Ambient → Ambient)
  (hsquare : ∀ a, f (familyProjection a)=familyProjection (lift a))
  (hlift : ∀ a, ambient (lift a)=F (ambient a))
  (hF : ∀ z : Ambient, 0<z.1.im → ContDiffAt ℂ ω F z)

include hsquare hlift in
/-- Exact local chart square for a joint-cover map. Both inverse
charts use the true joint covering map and the actual positive base lift. -/
theorem local_square (a b : Cover) (z : Ambient) (hz : z∈ambientChart.target) :
    f ((familyChart a).symm z)=
      (familyChart b).symm (F z) := by
  rw [familyChart_symm,familyChart_symm,hsquare]
  congr 1
  have he : ambient (lift (ambientChart.symm z))=F z := by
    rw [hlift]
    exact congrArg (F) (ambientChart.right_inv hz)
  rw [←he]
  exact (ambientChart.left_inv (ambientChart_source _)).symm

include hsquare hlift hF in
/-- Holomorphic descent of an actual joint-cover lift uses the same total
atlas and exact projection square on all covering points. -/
theorem joint_map_holomorphic : ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (f) := by
  intro p
  obtain ⟨a,rfl⟩ := familyProjection_surjective p
  have ha := familyChart_center a
  have hz : ambient a∈ambientChart.target := ambientChart.map_source (ambientChart_source a)
  have hb : ambient (lift a)∈(familyChart (lift a)).target := by
    have h := (familyChart (lift a)).map_source (familyChart_center (lift a))
    rwa [familyChart_at_center] at h
  have hInv := contMDiffAt_symm_of_mem_maximalAtlas
    (familyChart_maximal (lift a)) hb
  rw [hlift a] at hInv
  have hLift : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (F) (ambient a) :=
    contMDiffAt_iff_contDiffAt.mpr (hF (ambient a) a.1.property)
  have hlocal : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
      (f ∘ (familyChart a).symm) (ambient a) := by
    have hc : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
        ((familyChart (lift a)).symm ∘ F) (ambient a) :=
      hInv.comp _ hLift
    apply hc.congr_of_eventuallyEq
    filter_upwards [ambientChart.open_target.mem_nhds hz] with z hzt
    exact local_square f lift F hsquare hlift a (lift a) z hzt
  have hlocal' : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
      (f ∘ (familyChart a).symm) (familyChart a (familyProjection a)) := by
    rwa [familyChart_at_center]
  have hchart := contMDiffAt_of_mem_maximalAtlas (familyChart_maximal a) ha
  apply (hlocal'.comp _ hchart).congr_of_eventuallyEq
  filter_upwards [(familyChart a).open_source.mem_nhds ha] with q hq
  simp only [Function.comp_apply,(familyChart a).left_inv hq]
end PELJointHolomorphicLift318
