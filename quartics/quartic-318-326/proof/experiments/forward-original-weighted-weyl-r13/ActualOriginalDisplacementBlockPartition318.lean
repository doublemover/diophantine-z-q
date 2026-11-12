module
public import ActualOriginalCompleteFrequencyBudget318
public section
noncomputable section
namespace ActualOriginalDisplacementBlockPartition318
open QuadricCRTAssembly318 ActualOriginalCanonicalSupportBox318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCanonicalSliceBudget318
open ActualOriginalBoxOverlap318 ActualOriginalBoxSliceAggregation318
open ActualOriginalFrequencyBlockPartition318
open scoped BigOperators

@[expose] def displacementBlockKeys (L H : ℤ) : Finset ℤ :=
  (differences (centeredBox H)).image (fun h => (2*h.1.1)/L)
@[expose] def displacementBlockFiber (L H k : ℤ) : Finset (Coordinates ℤ) :=
  (differences (centeredBox H)).filter (fun h => (2*h.1.1)/L=k)
@[expose] def displacementSliceCost (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) : ℝ :=
  ∑ b∈overlap (Finset.Icc (-H) H) h.1.2,
  ∑ c∈overlap (Finset.Icc (-H) H) h.2.1.1,
  ∑ d∈overlap (Finset.Icc (-H) H) h.2.1.2,
  ∑ e∈overlap (Finset.Icc (-H) H) h.2.2,
    ‖sliceCorrelation κ w θ h (overlap (Finset.Icc (-H) H) h.1.1) b c d e‖

/-- The ACTUAL complete five-coordinate displacement/slice budget is
partitioned, preserving all four outer displacement coordinates and every
slice weight. No claim bounds multiplicity by the number of first frequencies. -/
theorem actual_canonical_displacement_block_partition (κ H L : ℤ)
    (w : Coordinates ℤ → ℂ) (θ : AddCircle (1 : ℝ)) :
    canonicalSliceBudget κ H w θ=
      ∑ k∈displacementBlockKeys L H,
        ∑ h∈displacementBlockFiber L H k, displacementSliceCost κ H w θ h := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun h hh => Finset.mem_image_of_mem (fun h => (2*h.1.1)/L) hh)
    (displacementSliceCost κ H w θ)

lemma actual_displacement_block_frequency (L H k : ℤ) (h : Coordinates ℤ)
    (hL : 0<L) (hh : h∈displacementBlockFiber L H k) :
    2*h.1.1∈Finset.Icc (k*L) (k*L+L-1) := by
  have he := (Finset.mem_filter.mp hh).2
  have hb := actual_frequency_in_quotient_block L (2*h.1.1) hL
  rwa [he] at hb

/-- The factor2 belongs to the original bilinear frequency. It is not
silently dropped when the actual displacement range is bounded. -/
lemma actual_original_displacement_frequency_range (H : ℤ) (h : Coordinates ℤ)
    (hh : h∈differences (centeredBox H)) :
    2*h.1.1∈Finset.Icc (-4*H) (4*H) := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  have hx0 : x.1.1∈Finset.Icc (-H) H :=
    (Finset.mem_product.mp (Finset.mem_product.mp hx).1).1
  have hy0 : y.1.1∈Finset.Icc (-H) H :=
    (Finset.mem_product.mp (Finset.mem_product.mp hy).1).1
  have hx' := Finset.mem_Icc.mp hx0
  have hy' := Finset.mem_Icc.mp hy0
  change 2*(x.1.1-y.1.1)∈Finset.Icc (-4*H) (4*H)
  apply Finset.mem_Icc.mpr
  omega

lemma actual_displacement_block_count (L H : ℤ) (hL : 0<L) :
    (displacementBlockKeys L H).card≤((4*H)/L-(-4*H)/L+1).toNat := by
  have hsub : displacementBlockKeys L H⊆Finset.Icc ((-4*H)/L) ((4*H)/L) := by
    intro k hk
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hk
    have hb := Finset.mem_Icc.mp (actual_original_displacement_frequency_range H h hh)
    exact Finset.mem_Icc.mpr ⟨Int.ediv_le_ediv hL hb.1,Int.ediv_le_ediv hL hb.2⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  omega

end ActualOriginalDisplacementBlockPartition318
