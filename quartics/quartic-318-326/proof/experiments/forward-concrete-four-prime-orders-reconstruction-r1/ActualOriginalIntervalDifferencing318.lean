module
public import ActualOriginalRectangularMinorMoment318
public section
noncomputable section
namespace ActualOriginalIntervalDifferencing318
open ActualOriginalBoxOverlap318
open scoped BigOperators ComplexConjugate

/-- Every ordered pair in a bounded integer interval is assigned its
literal signed difference. Empty intervals and both endpoints remain. -/
theorem actual_interval_differencing (H lo hi : ℤ) (hlo : -H≤lo) (hhi : hi≤H)
    (f : ℤ → ℂ) :
    (∑ x∈Finset.Icc lo hi, f x)*conj (∑ y∈Finset.Icc lo hi, f y)=
      ∑ h∈Finset.Icc (-2*H) (2*H),
        ∑ y∈overlap (Finset.Icc lo hi) h, f (h+y)*conj (f y) := by
  classical
  let s := Finset.Icc lo hi
  have hfiber : (∑ h∈Finset.Icc (-2*H) (2*H),
      ∑ xy∈(s.product s).filter (fun xy => xy.1-xy.2=h), f xy.1*conj (f xy.2))=
      ∑ xy∈s.product s, f xy.1*conj (f xy.2) := by
    apply Finset.sum_fiberwise_of_maps_to
    intro xy hxy
    have hx := Finset.mem_Icc.mp (Finset.mem_product.mp hxy).1
    have hy := Finset.mem_Icc.mp (Finset.mem_product.mp hxy).2
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ xy∈s.product s, f xy.1*conj (f xy.2) := by
      simp only [s,map_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_product]
    _ = _ := by
      rw [←hfiber]
      apply Finset.sum_congr rfl
      intro h hh
      symm
      unfold overlap
      apply Finset.sum_bij (fun y _ => (h+y,y))
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy'.2,hy'.1⟩,by simp⟩
      · intro y hy z hz he
        exact congrArg Prod.snd he
      · intro xy hxy
        obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hxy
        obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
        have he : h+xy.2=xy.1 := by rw [←hd]; abel
        exact ⟨xy.2,Finset.mem_filter.mpr ⟨hy,by rwa [he]⟩,Prod.ext he rfl⟩
      · intro y hy
        rfl

lemma actual_interval_square_bound (H lo hi : ℤ) (hlo : -H≤lo) (hhi : hi≤H)
    (f : ℤ → ℂ) :
    ‖∑ x∈Finset.Icc lo hi, f x‖^2≤
      ∑ h∈Finset.Icc (-2*H) (2*H),
        ‖∑ y∈overlap (Finset.Icc lo hi) h, f (h+y)*conj (f y)‖ := by
  calc
    _ = ‖(∑ x∈Finset.Icc lo hi, f x)*conj (∑ y∈Finset.Icc lo hi, f y)‖ := by
      simp only [norm_mul,Complex.norm_conj,pow_two]
    _ = _ := congrArg norm (actual_interval_differencing H lo hi hlo hhi f)
    _ ≤ _ := norm_sum_le _ _

end ActualOriginalIntervalDifferencing318
