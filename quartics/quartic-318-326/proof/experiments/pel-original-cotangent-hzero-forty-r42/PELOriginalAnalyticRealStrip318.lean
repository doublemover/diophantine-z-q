module
public import PELOriginalRealBranchIntervals318
public import PELOriginalAnalyticHalfPlaneSheets318
public section
noncomputable section
namespace PELOriginalAnalyticRealStrip318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalRealStripCover318 ComplexSphereCharts318
variable {i:Fin 4} (J:Interval i)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

@[expose] def totalSheet (e:J.BaseFiber) (z:ℂ) : CharacterBase i:=
  if hz:z∈J.Domain then J.sheet e ⟨z,hz⟩ else e.val
lemma totalSheet_eq (e:J.BaseFiber) (z:J.Domain) : totalSheet J e z=J.sheet e z := by
  simp only [totalSheet,dif_pos z.property]
lemma totalSheet_continuousOn (e:J.BaseFiber) : ContinuousOn (totalSheet J e) J.Domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he:J.Domain.domRestrict (totalSheet J e)=J.sheet e:=by
    funext z
    exact totalSheet_eq J e z
  rw [he]
  exact (J.sheet e).continuous

/-- The SAME whole-strip lift is holomorphic also AT every real point in
the interval, by the original cover's actual holomorphic local inverse. -/
theorem totalSheet_holomorphic (e:J.BaseFiber) (z:ℂ) (hz:z∈J.Domain) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (totalSheet J e) z := by
  have hproj:∀w∈J.Domain,normalizedMap i (totalSheet J e w)=(w:OnePoint ℂ):=by
    intro w hw
    rw [show totalSheet J e w=J.sheet e ⟨w,hw⟩ from totalSheet_eq J e ⟨w,hw⟩]
    exact J.sheet_projection e ⟨w,hw⟩
  apply ComplexCurveContinuousLift318.lift_at (normalizedMap i)
    ((normalizedMap i) ⁻¹' J.image) J.covering.isLocalHomeomorphOn
    (totalSheet J e) ((↑):ℂ→OnePoint ℂ) z
  · change normalizedMap i (totalSheet J e z)∈J.image
    rw [hproj z hz]
    exact ⟨z,hz,rfl⟩
  · exact PELOriginalNormalizedDoubleCover318.holomorphic i _
  · exact (totalSheet_continuousOn J e z hz).continuousAt
      ((ComplexVerticalStrip318.strip_open J.isOpen).mem_nhds hz)
  · exact ComplexSphereAffineAutomorphisms318.coe_holomorphic z
  · filter_upwards [(ComplexVerticalStrip318.strip_open J.isOpen).mem_nhds hz] with w hw
    exact hproj w hw

/-- Each upper original global sheet and its SINGLE matched lower sheet
are restrictions of one genuinely holomorphic lift through the WHOLE real
interval. No seam continuity or analytic extension is supplied as input. -/
theorem analytic_transition (e:PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true) :
    ∃F:ℂ→CharacterBase i,
      (∀z∈J.Domain,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F z) ∧
      (∀z:J.HalfDomain true,
        PELOriginalGlobalHalfPlaneSheets318.sheet i true e (J.toHalf true z)=F z.val) ∧
      (∀z:J.HalfDomain false,
        PELOriginalGlobalHalfPlaneSheets318.sheet i false (J.transition e) (J.toHalf false z)=F z.val) := by
  let e':J.BaseFiber:=(J.sideLabels true).symm e
  refine ⟨totalSheet J e',totalSheet_holomorphic J e',?_,?_⟩
  · intro z
    rw [show totalSheet J e' z.val=J.sheet e' (J.toStrip true z) from totalSheet_eq J e' (J.toStrip true z)]
    simpa only [e',Equiv.apply_symm_apply] using J.sheet_agrees true e' z
  · intro z
    rw [show totalSheet J e' z.val=J.sheet e' (J.toStrip false z) from totalSheet_eq J e' (J.toStrip false z)]
    exact J.sheet_agrees false e' z

/-- ALL FOUR actual complementary real components receive the same
constructed analytic continuation statement; branch order is produced. -/
theorem all_interval_continuations (j:Fin 4)
    (e:PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true) :
    ∃F:ℂ→CharacterBase i,
      (∀z∈((PELOriginalRealBranchIntervals318.ordering i).interval j).Domain,
        ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F z) ∧
      (∀z:((PELOriginalRealBranchIntervals318.ordering i).interval j).HalfDomain true,
        PELOriginalGlobalHalfPlaneSheets318.sheet i true e
          (((PELOriginalRealBranchIntervals318.ordering i).interval j).toHalf true z)=F z.val) ∧
      (∀z:((PELOriginalRealBranchIntervals318.ordering i).interval j).HalfDomain false,
        PELOriginalGlobalHalfPlaneSheets318.sheet i false
          (PELOriginalRealBranchIntervals318.actualTransition i j e)
          (((PELOriginalRealBranchIntervals318.ordering i).interval j).toHalf false z)=F z.val) :=
  analytic_transition ((PELOriginalRealBranchIntervals318.ordering i).interval j) e
end PELOriginalAnalyticRealStrip318
