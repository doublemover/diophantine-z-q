module
public import ComplexLineLatticeAtlas318
public import Mathlib.Analysis.Complex.Liouville
public section
noncomputable section
namespace ComplexPeriodicCoefficient318
open Set Filter Topology ComplexLineLatticeAtlas318
variable (L:AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Quotient L)]
variable (f:ℂ→ℂ) (hf:∀z,AnalyticAt ℂ f z)
  (hperiod:∀a∈L,∀z,f (z+a)=f z)
lemma same_fibers (z w:ℂ) (h:projection L z=projection L w) : f z=f w := by
  have hm:z-w∈L:=by
    apply QuotientAddGroup.eq_zero_iff.mp
    change (QuotientAddGroup.mk' L)(z-w)=0
    rw [map_sub,h,sub_self]
  have he:=hperiod (z-w) hm w
  have hz:w+(z-w)=z:=by ring
  simpa only [hz] using he
@[expose] def descended : Quotient L→ℂ:=
  Quotient.lift f (fun z w h=>same_fibers L f hperiod z w (Quotient.sound h))
lemma descended_continuous : Continuous (descended L f hperiod) :=
  (continuous_iff_continuousAt.mpr (fun z=>(hf z).continuousAt)).quotient_lift _

/-- Compactness is applied to the GENUINE lattice quotient of the entire
periodic coefficient. No unproved bounded fundamental region is supplied. -/
theorem eq_at_zero : ∀z,f z=f 0 := by
  have hb:Bornology.IsBounded (range f):=by
    apply (isCompact_range (descended_continuous L f hf hperiod)).isBounded.subset
    rintro w ⟨z,rfl⟩
    exact ⟨projection L z,rfl⟩
  obtain ⟨c,hc⟩:=(show Differentiable ℂ f from fun z=>(hf z).differentiableAt)
    .exists_const_forall_eq_of_bounded hb
  intro z
  exact (hc z).trans (hc 0).symm
end ComplexPeriodicCoefficient318
