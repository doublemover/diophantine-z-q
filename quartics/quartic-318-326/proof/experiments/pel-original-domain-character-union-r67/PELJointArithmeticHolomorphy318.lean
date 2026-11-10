module
public import PELJointArithmeticLift318
public section
noncomputable section
namespace PELJointArithmeticHolomorphy318
open QuaternionicRealPeriod318 QuaternionicUnitPeriodTransport318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELHolomorphicFamilyProjection318 PELOriginalHolomorphicFibers318
open PELJointArithmeticLift318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
variable (u : orderˣ) (hu : (unitMatrix representation order u).det=1)

/-- Exact local chart square for the joint arithmetic map. Both inverse
charts use the true joint covering map and the actual positive base lift. -/
theorem local_square (a b : Cover) (z : Ambient) (hz : z∈ambientChart.target) :
    totalAction u hu ((familyChart a).symm z)=
      (familyChart b).symm (ambientLift u z) := by
  rw [familyChart_symm,familyChart_symm,projection_square]
  congr 1
  have he : ambient (lift u hu (ambientChart.symm z))=ambientLift u z := by
    rw [lift_ambient]
    exact congrArg (ambientLift u) (ambientChart.right_inv hz)
  rw [←he]
  exact (ambientChart.left_inv (ambientChart_source _)).symm

/-- Arithmetic base change is holomorphic on the JOINT threefold; this is
strictly stronger than having a biholomorphism separately on each fiber. -/
theorem totalAction_holomorphic : ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (totalAction u hu) := by
  intro p
  obtain ⟨a,rfl⟩ := familyProjection_surjective p
  have ha := familyChart_center a
  have hz : ambient a∈ambientChart.target := ambientChart.map_source (ambientChart_source a)
  have hb : ambient (lift u hu a)∈(familyChart (lift u hu a)).target := by
    have h := (familyChart (lift u hu a)).map_source (familyChart_center (lift u hu a))
    rwa [familyChart_at_center] at h
  have hInv := contMDiffAt_symm_of_mem_maximalAtlas
    (familyChart_maximal (lift u hu a)) hb
  have hLift : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (ambientLift u) (ambient a) :=
    contMDiffAt_iff_contDiffAt.mpr (ambientLift_analytic u hu (ambient a) a.1.property).contDiffAt
  have hlocal : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
      (totalAction u hu ∘ (familyChart a).symm) (ambient a) := by
    have hc : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
        ((familyChart (lift u hu a)).symm ∘ ambientLift u) (ambient a) :=
      hInv.comp _ hLift
    apply hc.congr_of_eventuallyEq
    filter_upwards [ambientChart.open_target.mem_nhds hz] with z hzt
    exact local_square u hu a (lift u hu a) z hzt
  have hlocal' : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω
      (totalAction u hu ∘ (familyChart a).symm) (familyChart a (familyProjection a)) := by
    rwa [familyChart_at_center]
  have hchart := contMDiffAt_of_mem_maximalAtlas (familyChart_maximal a) ha
  apply (hlocal'.comp _ hchart).congr_of_eventuallyEq
  filter_upwards [(familyChart a).open_source.mem_nhds ha] with q hq
  simp only [Function.comp_apply,(familyChart a).left_inv hq]
end PELJointArithmeticHolomorphy318
