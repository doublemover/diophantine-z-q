module
public import DiscreteComplexPeriodAtlas318
public import Mathlib.Analysis.Normed.Group.Bounded
public section
noncomputable section
namespace CompactPeriodNormBound318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Set Filter Topology
variable (L : AddSubgroup ComplexVectors) [DiscreteTopology L] [CompactSpace (Quotient L)]
  (N : ComplexVectors → ℝ) (hN : Continuous N) (hp : ∀ (l : L) z,N (z+l.val)=N z)

include hp in
lemma equal_fibers (z w : ComplexVectors) (h : projection L z=projection L w) : N z=N w := by
  have hm : z-w ∈ L := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (QuotientAddGroup.mk' L) (z-w)=0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have he := hp ⟨z-w,hm⟩ w
  have hw : w+(z-w)=z := by abel
  simpa only [hw] using he

@[expose] def descended (q : Quotient L) : ℝ := N ((quotient_surjective L q).choose)
include hp in
lemma descended_projection (z : ComplexVectors) : descended L N (projection L z)=N z :=
  equal_fibers L N hp _ z (quotient_surjective L (projection L z)).choose_spec

include hN hp in
lemma descended_continuous : Continuous (descended L N) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,rfl⟩ := quotient_surjective L q
  have hz := localChart_center L z
  have hc := hN.continuousAt.comp ((localChart L z).continuousAt hz)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(localChart L z).open_source.mem_nhds hz] with p hp'
  have he : projection L (localChart L z p)=p := by
    simpa only [localChart_symm] using (localChart L z).left_inv hp'
  rw [←he]
  exact descended_projection L N hp (localChart L z p)

/-- Actual compactness of the ORIGINAL period quotient bounds any
continuous periodic norm. The scalar function need not itself be periodic. -/
include hN hp in
theorem bounded_above : ∃ C : ℝ, ∀ z,N z≤C := by
  obtain ⟨C,hC⟩ := (isCompact_range (descended_continuous L N hN hp)).bddAbove
  refine ⟨C,fun z => ?_⟩
  rw [←descended_projection L N hp z]
  exact hC (mem_range_self (projection L z))

/-- This is boundedness of the entire complex-valued function's range,
not merely a bound on a chosen lattice or fundamental-domain subset. -/
theorem bounded_range (f : ComplexVectors → ℂ) (hf : Continuous f)
    (hp : ∀ (l : L) z,‖f (z+l.val)‖=‖f z‖) : Bornology.IsBounded (range f) := by
  obtain ⟨C,hC⟩ := bounded_above L (fun z => ‖f z‖) hf.norm hp
  exact isBounded_iff_forall_norm_le.mpr ⟨C,by rintro _ ⟨z,rfl⟩; exact hC z⟩
end CompactPeriodNormBound318
