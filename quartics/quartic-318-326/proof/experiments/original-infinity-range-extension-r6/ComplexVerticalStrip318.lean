module
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace ComplexVerticalStrip318
open Set
open LegendreHalfPlaneAnalyticSheets318
@[expose] def strip (J:Set ℝ):Set ℂ:=Complex.re ⁻¹' J
@[expose] def halfStrip (J:Set ℝ) (upper:Bool):Set ℂ:=strip J∩domain upper
lemma strip_open {J:Set ℝ} (hJ:IsOpen J) : IsOpen (strip J):=hJ.preimage Complex.continuous_re
lemma strip_convex {J:Set ℝ} (hJ:Convex ℝ J) : Convex ℝ (strip J):=
  hJ.linear_preimage Complex.reLm
lemma strip_nonempty {J:Set ℝ} (hJ:J.Nonempty) : (strip J).Nonempty := by
  obtain ⟨x,hx⟩:=hJ
  exact ⟨(x:ℂ),by simpa only [strip,mem_preimage,Complex.ofReal_re] using hx⟩
lemma strip_simplyConnected {J:Set ℝ} (hc:Convex ℝ J) (hn:J.Nonempty) : IsSimplyConnected (strip J) := by
  letI : ContractibleSpace (strip J):=(strip_convex hc).contractibleSpace (strip_nonempty hn)
  exact inferInstance
lemma halfStrip_open {J:Set ℝ} (hJ:IsOpen J) (upper:Bool) : IsOpen (halfStrip J upper):=
  (strip_open hJ).inter (domain_open upper)
lemma halfStrip_convex {J:Set ℝ} (hJ:Convex ℝ J) (upper:Bool) : Convex ℝ (halfStrip J upper):=
  (strip_convex hJ).inter (domain_convex upper)
@[expose] def sidePoint (x:ℝ) (upper:Bool) : ℂ:=(x:ℂ)+(if upper then Complex.I else -Complex.I)
lemma sidePoint_mem {J:Set ℝ} {x:ℝ} (hx:x∈J) (upper:Bool) : sidePoint x upper∈halfStrip J upper := by
  constructor
  · cases upper <;> simpa [strip,sidePoint] using hx
  · cases upper <;> norm_num [sidePoint,domain,side]
lemma halfStrip_nonempty {J:Set ℝ} (hJ:J.Nonempty) (upper:Bool) : (halfStrip J upper).Nonempty := by
  obtain ⟨x,hx⟩:=hJ
  exact ⟨sidePoint x upper,sidePoint_mem hx upper⟩
lemma halfStrip_simplyConnected {J:Set ℝ} (hc:Convex ℝ J) (hn:J.Nonempty) (upper:Bool) :
    IsSimplyConnected (halfStrip J upper) := by
  letI : ContractibleSpace (halfStrip J upper):=
    (halfStrip_convex hc upper).contractibleSpace (halfStrip_nonempty hn upper)
  exact inferInstance
end ComplexVerticalStrip318
