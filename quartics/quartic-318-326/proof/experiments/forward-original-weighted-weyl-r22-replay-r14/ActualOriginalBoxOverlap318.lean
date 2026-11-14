module
public import ActualOriginalCorrelationBasePoints318
public section
noncomputable section
namespace ActualOriginalBoxOverlap318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318
open ActualOriginalCorrelationBasePoints318
open scoped BigOperators

@[expose] def overlap (s : Finset ℤ) (h : ℤ) : Finset ℤ := s.filter (fun y => h+y∈s)

/-- Original box displacement fibers are the product of the FIVE actual
overlap sets. This is index-set coverage, not separability of the weight. -/
theorem actual_box_base_points (s₀ s₁ s₂ s₃ s₄ : Finset ℤ) (h : Coordinates ℤ) :
    basePoints (originalBox s₀ s₁ s₂ s₃ s₄) h=
      originalBox (overlap s₀ h.1.1) (overlap s₁ h.1.2)
        (overlap s₂ h.2.1.1) (overlap s₃ h.2.1.2) (overlap s₄ h.2.2) := by
  classical
  ext y
  simp only [basePoints,overlap,originalBox,Finset.mem_filter,Finset.mem_product,
    Prod.fst_add,Prod.snd_add]
  tauto

/-- For integer intervals the overlap bounds are explicit and include
all endpoint and empty-overlap cases. -/
theorem actual_interval_overlap (lo hi h : ℤ) :
    overlap (Finset.Icc lo hi) h=
      Finset.Icc (max lo (lo-h)) (min hi (hi-h)) := by
  ext y
  simp only [overlap,Finset.mem_filter,Finset.mem_Icc,max_le_iff,le_min_iff]
  omega

/-- Integer closed interval sums are actual consecutive-line sums,
including hi<lo, where the natural interval length is zero. -/
theorem actual_integer_interval_sum (f : ℤ → ℂ) (lo hi : ℤ) :
    (∑ a ∈ Finset.Icc lo hi, f a)=
      ∑ j ∈ Finset.range (hi-lo+1).toNat, f (lo+(j : ℤ)) := by
  symm
  apply Finset.sum_bij (fun j _ => lo+(j : ℤ))
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_Icc.mpr
    omega
  · intro j hj k hk he
    omega
  · intro a ha
    obtain ⟨hal,hah⟩ := Finset.mem_Icc.mp ha
    refine ⟨(a-lo).toNat,Finset.mem_range.mpr (by omega),by omega⟩
  · intro j hj
    rfl

end ActualOriginalBoxOverlap318
