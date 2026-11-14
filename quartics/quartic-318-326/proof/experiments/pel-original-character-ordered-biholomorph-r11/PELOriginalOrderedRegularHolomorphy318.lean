module
public import LegendreCurveFiniteGermHolomorphy318
public import PELOriginalOrderedCharacterContinuity318
public section
noncomputable section
namespace PELOriginalOrderedRegularHolomorphy318
open Set Filter
open scoped Topology Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactContinuity318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalOrderedCharacterContinuity318
open PELOriginalCharacterQuotient318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold
variable (i:Fin 4)
local instance :ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane (parameter i)):=
  LegendreCompletedComplexAtlas318.chartedSpace _
local instance :IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane (parameter i)):=
  LegendreCompletedComplexAtlas318.complex_manifold _

/-- Exact polynomial finite coordinates of the SAME Scheme-induced
comparison, pulled back to the original regular source locus. -/
theorem source_regular (p:UnlevelledBase) (hp:p∈RegularSource):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i ∘ toCharacter i) p:=by
  have ht:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(regularGerm p hp x).val.1) p:=by
    apply (PELOriginalContactRootHolomorphy318.base_holomorphic p hp).congr_of_eventuallyEq
    filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
    simp only [regularGerm,dif_pos hx]
  have hz:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(regularGerm p hp x).val.2 k) p:=by
    intro k
    apply (PELOriginalContactRootHolomorphy318.roots_holomorphic p hp k).congr_of_eventuallyEq
    filter_upwards [PELOriginalContactRegularDensity318.regular_open.mem_nhds hp] with x hx
    simp only [regularGerm,dif_pos hx]
  let g:=fun x=>PELOriginalOrderedFiniteAnalyticCoordinates318.finiteMap i (regularGerm p hp x)
  have hx:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(g x).val.1) p:=by
    simp only [g,PELOriginalOrderedFiniteAnalyticCoordinates318.coordinate_x]
    exact contMDiffAt_const.mul (ht.sub contMDiffAt_const)
  have hy:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x=>(g x).val.2) p:=by
    simp only [g,PELOriginalOrderedFiniteAnalyticCoordinates318.coordinate_y]
    exact contMDiffAt_const.mul (((hz _).mul (hz _)).mul (hz _))
  apply (LegendreCurveFiniteGermHolomorphy318.finite (parameter i) g p hx hy).congr_of_eventuallyEq
  filter_upwards [regular_map_germ p hp] with x hx
  change comparison i (toCharacter i x)=_
  rw [source_square,PELOriginalCompletedContactBiholomorph318.comparison_value,hx,
    PELOriginalOrderedCompletedChartSquares318.finite_square]
end PELOriginalOrderedRegularHolomorphy318
