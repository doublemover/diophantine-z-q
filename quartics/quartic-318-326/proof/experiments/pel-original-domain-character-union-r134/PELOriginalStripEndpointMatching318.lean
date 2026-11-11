module
public import PELOriginalHalfPlaneArcSheets318
public section
noncomputable section
namespace PELOriginalStripEndpointMatching318
open Set Filter
open scoped Topology OnePoint
open PELOriginalCharacterQuotient318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalRealStripCover318 PELOriginalAnalyticRealStrip318
open PELOriginalHalfPlaneArcSheets318 LegendreHalfPlaneAnalyticSheets318
variable {i:Fin 4} (J:Interval i)
local instance : SimplyConnectedSpace J.Domain:=
  ComplexVerticalStrip318.strip_simplyConnected J.convex ⟨J.point,J.point_mem⟩
local instance : LocallyPathConnectedSpace J.Domain:=
  (ComplexVerticalStrip318.strip_open J.isOpen).locallyPathConnectedSpace

/-- The genuine real seam value obtained by the whole original strip
lift. This is not a chosen limit of independently indexed sheet points. -/
@[expose] def seamValue (upper:Bool) (e:BaseFiber i upper) (a:ℝ) (ha:a∈J.carrier) : CharacterBase i:=
  J.sheet ((J.sideLabels upper).symm e) ⟨(a:ℂ),ha⟩

/-- Equality of actual real seam points is exactly the already constructed
constant interval transition on the two complete original fibers. -/
theorem seam_eq_iff (e:BaseFiber i true) (f:BaseFiber i false) (a:ℝ) (ha:a∈J.carrier) :
    seamValue J true e a ha=seamValue J false f a ha ↔ J.transition e=f := by
  have hinj:Function.Injective (fun d:J.BaseFiber=>J.sheet d ⟨(a:ℂ),ha⟩):=
    SimplyConnectedCoverSheets318.sheet_injective_at (PELOriginalNormalizedDoubleCover318.normalizedMap i)
      J.image J.covering J.baseMap J.baseMap_mem J.basepoint ⟨(a:ℂ),ha⟩
  constructor
  · intro h
    have hd:((J.sideLabels true).symm e)=((J.sideLabels false).symm f):=hinj h
    change J.sideLabels false ((J.sideLabels true).symm e)=f
    rw [hd,Equiv.apply_symm_apply]
  · intro h
    have hd:((J.sideLabels true).symm e)=((J.sideLabels false).symm f):=by
      apply (J.sideLabels false).injective
      simpa only [Equiv.apply_symm_apply] using h
    exact congrArg (fun d:J.BaseFiber=>J.sheet d ⟨(a:ℂ),ha⟩) hd

/-- A continuous original crossing arc on one global halfplane sheet has
at an unbranched real endpoint exactly its actual strip seam value.
Continuity and equality on the interior are USED to derive the endpoint,
not supplied as a boundary-identification assumption. The approaching
filter can be either endpoint side of the original interval path. -/
theorem endpoint (upper:Bool) (base:ℝ→ℂ) (lift:ℝ→CharacterBase i)
    (e:BaseFiber i upper)
    (hs:∀t∈Interior,base t∈domain upper)
    (he:∀(t:ℝ)(ht:t∈Interior),sheet i upper e ⟨base t,hs t ht⟩=lift t)
    (t₀ a:ℝ) (ha:a∈J.carrier) (hbase:base t₀=(a:ℂ))
    (hb:ContinuousAt base t₀) (hl:ContinuousAt lift t₀)
    (L:Filter ℝ) [NeBot L] (hL:Tendsto id L (𝓝 t₀))
    (hinter:∀ᶠ t in L,t∈Interior) :
    lift t₀=seamValue J upper e a ha := by
  let d:J.BaseFiber:=(J.sideLabels upper).symm e
  have hm:base t₀∈J.Domain:=by rw [hbase];exact ha
  have ht:Tendsto base L (𝓝 (base t₀)):=hb.tendsto.comp hL
  have hstrip:∀ᶠ t in L,base t∈J.Domain:=
    ht.eventually ((ComplexVerticalStrip318.strip_open J.isOpen).mem_nhds hm)
  have hc:ContinuousAt (totalSheet J d) (base t₀):=
    (totalSheet_continuousOn J d _ hm).continuousAt
      ((ComplexVerticalStrip318.strip_open J.isOpen).mem_nhds hm)
  have hlimit:Tendsto (fun t=>totalSheet J d (base t)) L
      (𝓝 (seamValue J upper e a ha)):=by
    have hh:=hc.tendsto.comp ht
    have hv:totalSheet J d (base t₀)=seamValue J upper e a ha:=by
      rw [hbase]
      exact totalSheet_eq J d ⟨(a:ℂ),ha⟩
    simpa only [hv] using hh
  have hevent:lift =ᶠ[L] fun t=>totalSheet J d (base t):=by
    filter_upwards [hinter,hstrip] with t ht hs'
    let z:J.HalfDomain upper:=⟨base t,hs',hs t ht⟩
    calc
      lift t=sheet i upper e ⟨base t,hs t ht⟩:=(he t ht).symm
      _=J.sheet d (J.toStrip upper z):=by
        simpa only [d,Equiv.apply_symm_apply] using J.sheet_agrees upper d z
      _=totalSheet J d (base t):=(totalSheet_eq J d (J.toStrip upper z)).symm
  exact tendsto_nhds_unique ((hl.tendsto.comp hL).congr' hevent) hlimit
end PELOriginalStripEndpointMatching318
