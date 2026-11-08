module
public import RotatedEndSeparation318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups
namespace FiniteCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Distinct actual ends, with duplicate coset representatives removed by their
proved equality of high cusp neighborhoods. -/
@[expose] def endRegions (N:ℕ) : Set (Set (Base (image N))) :=
  RotatedProjection318.neighborhood N '' FiniteCuspCoverage318.rotations N
abbrev End (N:ℕ) := endRegions N

instance ends_finite (N:ℕ) [NeZero N] : Finite (End N) :=
  ((FiniteCuspCoverage318.rotations_finite N).image (RotatedProjection318.neighborhood N)).to_subtype

instance ends_nonempty (N:ℕ) : Nonempty (End N) := by
  let q:SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma1 N:=⟦1⟧
  exact ⟨⟨_,q.out⁻¹,⟨q,rfl⟩,rfl⟩⟩

@[expose] def representative (N:ℕ) (c:End N) : SL(2,ℤ) := c.property.choose

theorem representative_mem (N:ℕ) (c:End N) :
    representative N c∈FiniteCuspCoverage318.rotations N := c.property.choose_spec.1

theorem representative_region (N:ℕ) (c:End N) :
    RotatedProjection318.neighborhood N (representative N c)=c.val := c.property.choose_spec.2

/-- Distinct selected ends have disjoint actual open neighborhoods. -/
theorem regions_disjoint (N:ℕ) (c d:End N) (hcd:c≠d) : Disjoint c.val d.val := by
  rcases RotatedEndSeparation318.neighborhoods_equal_or_disjoint N (representative N c) (representative N d) with he|hd
  · rw [representative_region,representative_region] at he
    exact False.elim (hcd (Subtype.ext he))
  · simpa only [representative_region] using hd

theorem region_nonempty (N:ℕ) (g:SL(2,ℤ)) (A:ℝ) :
    (FiniteCuspCoverage318.cuspRegion N g A).Nonempty := by
  let tau:UpperHalfPlane:=⟨(max A 0+1)*Complex.I,by simp;linarith [le_max_right A 0]⟩
  refine ⟨quotientMap N (g•tau),tau,?_,rfl⟩
  change A<tau.im
  dsimp [tau]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,Complex.ofReal_im,
    Complex.I_re,mul_zero,add_zero,Complex.add_re,Complex.one_re]
  linarith [le_max_left A 0]

/-- Equality at height two identifies the same end at every height. -/
theorem region_eq_of_neighborhood_eq (N:ℕ) (g h:SL(2,ℤ))
    (he:RotatedProjection318.neighborhood N g=RotatedProjection318.neighborhood N h) (A:ℝ) :
    FiniteCuspCoverage318.cuspRegion N g A=FiniteCuspCoverage318.cuspRegion N h A := by
  apply RotatedEndSeparation318.regions_equal_of_intersect N g h 2 2 (by norm_num) (by norm_num) _ A
  obtain ⟨b,hb⟩:=region_nonempty N g 2
  apply Set.not_disjoint_iff.mpr
  change b∈RotatedProjection318.neighborhood N g at hb
  exact ⟨b,hb,show b∈RotatedProjection318.neighborhood N h from he ▸ hb⟩

/-- Compact core and the finitely many *distinct* ends cover the genuine quotient. -/
theorem compact_core_and_distinct_ends (N:ℕ) (A:ℝ) (b:Base (image N)) :
    b∈FiniteCuspCoverage318.compactCore N A ∨
      ∃c:End N,b∈FiniteCuspCoverage318.cuspRegion N (representative N c) A := by
  rcases FiniteCuspCoverage318.compact_core_and_cusps N A b with hb|⟨g,hg,hb⟩
  · exact Or.inl hb
  · let c:End N:=⟨RotatedProjection318.neighborhood N g,⟨g,hg,rfl⟩⟩
    refine Or.inr ⟨c,?_⟩
    rw [region_eq_of_neighborhood_eq N (representative N c) g (representative_region N c) A]
    exact hb

end FiniteCuspEnds318
