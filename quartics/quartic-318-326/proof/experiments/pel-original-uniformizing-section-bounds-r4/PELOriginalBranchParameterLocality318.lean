module
public import PELOriginalInfinityBranchSource318
public import ComplexCurvePartialInverse318
public section
noncomputable section
namespace PELOriginalBranchParameterLocality318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalLiteralBranchParameters318
variable {i:Fin 4} {p:CharacterBase i} {B:ℂ→OnePoint ℂ}
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
variable (P:SquareParametrization i p B)

@[expose] def source (w:ℂ) : CharacterBase i:=P.chart.symm (P.inverseChange w)
@[expose] def coordinate (x:CharacterBase i) : ℂ:=P.changeMap (P.chart x)
lemma source_zero : source P 0=p := by
  rw [source,P.inverse_zero,←P.center_zero,P.chart.left_inv P.center_mem]
lemma coordinate_zero : coordinate P p=0 := by rw [coordinate,P.center_zero,P.change_zero]
lemma chart_inverse_zero : P.chart.symm 0=p := by rw [←P.center_zero,P.chart.left_inv P.center_mem]

/-- The stored inverse chart analyticity implies actual forward chart
analyticity by the genuine local inverse theorem. No omitted forward
chart signature is silently assumed when returning to the source atlas. -/
lemma chart_holomorphic : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω P.chart p := by
  have ht:0∈P.chart.target:=by rw [←P.center_zero];exact P.chart.map_source P.center_mem
  have hh:=ComplexCurvePartialInverse318.inverse_at P.chart.symm 0 ht
    (P.chart_inverse_holomorphic 0 ht)
  change ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω P.chart (P.chart.symm 0) at hh
  rw [chart_inverse_zero P] at hh
  exact hh
lemma coordinate_holomorphic : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coordinate P) p := by
  have hc:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω P.changeMap (P.chart p):=by
    rw [P.center_zero]
    exact contMDiffAt_iff_contDiffAt.mpr P.change_analytic.contDiffAt
  exact hc.comp p (chart_holomorphic P)

/-- The literal branch parametrization reaches EVERY nearby original
point, with this actual analytic inverse coordinate. This is stronger
than merely knowing the formula along the parametrized image. -/
lemma source_coordinate : (fun x=>source P (coordinate P x))=ᶠ[𝓝 p] id := by
  have hc:Tendsto P.chart (𝓝 p) (𝓝 (0:ℂ)):=by
    simpa only [P.center_zero] using (P.chart.continuousAt P.center_mem)
  filter_upwards [hc.eventually P.left_inverse,P.chart.open_source.mem_nhds P.center_mem] with x hx hs
  change P.chart.symm (P.inverseChange (P.changeMap (P.chart x)))=x
  rw [hx,P.chart.left_inv hs]
lemma coordinate_source : (fun w=>coordinate P (source P w))=ᶠ[𝓝 (0:ℂ)] id := by
  filter_upwards [P.projection,P.right_inverse] with w hw hr
  change P.changeMap (P.chart (P.chart.symm (P.inverseChange w)))=w
  rw [P.chart.right_inv hw.1,hr]

/-- Analyticity of a map along the actual literal branch parameter
transfers to analyticity at the ORIGINAL source point, for any independent
complex target atlas. Actual inverse coordinates and neighborhood equality
are constructed above, not supplied as an identification assumption. -/
theorem transfer {N:Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω N] (f:CharacterBase i→N)
    (hf:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>f (source P w)) 0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f p := by
  have hf':ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>f (source P w)) (coordinate P p):=by
    rw [coordinate_zero]
    exact hf
  have hh:=hf'.comp p (coordinate_holomorphic P)
  apply hh.congr_of_eventuallyEq
  filter_upwards [source_coordinate P] with x hx
  change f x=f (source P (coordinate P x))
  rw [hx]
end PELOriginalBranchParameterLocality318
