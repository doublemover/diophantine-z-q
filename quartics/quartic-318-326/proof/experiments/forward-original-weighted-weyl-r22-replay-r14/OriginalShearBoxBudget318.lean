module
public import OriginalUniformEliminantHeight318
public section
noncomputable section
namespace OriginalShearBoxBudget318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318
open OriginalSieveFrame318 OriginalBoundedIntegerShear318 OriginalOffsetEliminant318
open OriginalUniformEliminantHeight318 IntegerResidueBoxCount318
set_option maxHeartbeats 6000000

lemma embed_box (a : Vector ℤ) : Box a ‖embed a‖ := by
  have h (i : Fin 3) : |embed a i|≤‖embed a‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (embed a) i
  exact ⟨by simpa [embed] using h 0,by simpa [embed] using h 1,by simpa [embed] using h 2⟩

lemma box_mono (a : Vector ℤ) {L H : ℝ} (ha : Box a L) (hLH : L≤H) : Box a H :=
  ⟨ha.1.trans hLH,ha.2.1.trans hLH,ha.2.2.trans hLH⟩

lemma box_add (a b : Vector ℤ) (L H : ℝ) (ha : Box a L) (hb : Box b H) : Box (a+b) (L+H) := by
  have h (x y : ℤ) (hx : |(x:ℝ)|≤L) (hy : |(y:ℝ)|≤H) : |((x+y:ℤ):ℝ)|≤L+H := by
    rw [Int.cast_add]
    exact (abs_add _ _).trans (add_le_add hx hy)
  exact ⟨h _ _ ha.1 hb.1,h _ _ ha.2.1 hb.2.1,h _ _ ha.2.2 hb.2.2⟩

lemma box_smul (a : Vector ℤ) (n : ℤ) (L H : ℝ) (hL : 0≤L)
    (ha : Box a L) (hn : |(n:ℝ)|≤H) : Box (n • a) (H*L) := by
  have h (x : ℤ) (hx : |(x:ℝ)|≤L) : |((n*x:ℤ):ℝ)|≤H*L := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul hn hx (abs_nonneg _) ((abs_nonneg _).trans hn)
  simpa only [Prod.smul_mk,zsmul_eq_mul] using
    (show Box (n*a.1,n*a.2.1,n*a.2.2) (H*L) from ⟨h _ ha.1,h _ ha.2.1,h _ ha.2.2⟩)

@[expose] def heightRadius (A B : ℕ) (W : ℝ) := ((A:ℝ)+(B:ℝ)+10)*W

/-- An explicit coordinate budget on ALL enlarged offsets and all25
candidate directions, built from the actual basis and third minimum.
A coarse polynomial size is enough inside the logarithm; no height input
is left to the point-tail caller. -/
theorem uniform_box (u v w z : Vector ℤ)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (A B i j : ℕ) (hi : i<5) (hj : j<5)
    (a : Interval A) (b : Interval B) :
    Box (offset u v a.1 b.1) (heightRadius A B ‖embed w‖) ∧
      Box (shear (i:ℤ) (j:ℤ) u v z) (heightRadius A B ‖embed w‖) := by
  let W := ‖embed w‖
  have hW : 0≤W := norm_nonneg _
  have hu : Box u W := box_mono u (embed_box u) (huv.trans hvw)
  have hv : Box v W := box_mono v (embed_box v) hvw
  have hZ : Box z (2*W) := box_mono z (embed_box z) hz
  have ha : |(a.1:ℝ)|≤(A:ℝ) := by
    have hh := abs_le.mpr (Finset.mem_Icc.mp a.2)
    exact_mod_cast hh
  have hb : |(b.1:ℝ)|≤(B:ℝ) := by
    have hh := abs_le.mpr (Finset.mem_Icc.mp b.2)
    exact_mod_cast hh
  have hI : |((i:ℤ):ℝ)|≤4 := by
    simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg i)]
    exact_mod_cast (show i≤4 by omega)
  have hJ : |((j:ℤ):ℝ)|≤4 := by
    simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg j)]
    exact_mod_cast (show j≤4 by omega)
  have ho := box_add (a.1 • u) (b.1 • v) ((A:ℝ)*W) ((B:ℝ)*W)
    (box_smul u a.1 W A hW hu ha) (box_smul v b.1 W B hW hv hb)
  have hd := box_add (z+(i:ℤ) • u) ((j:ℤ) • v) (2*W+4*W) (4*W)
    (box_add z ((i:ℤ) • u) (2*W) (4*W) hZ (box_smul u (i:ℤ) W 4 hW hu hI))
    (box_smul v (j:ℤ) W 4 hW hv hJ)
  refine ⟨box_mono _ ho ?_,box_mono _ hd ?_⟩
  · dsimp [heightRadius,W]
    nlinarith [norm_nonneg (embed w)]
  · dsimp [heightRadius,W]
    nlinarith [norm_nonneg (embed w),mul_nonneg (Nat.cast_nonneg A) (norm_nonneg (embed w)),
      mul_nonneg (Nat.cast_nonneg B) (norm_nonneg (embed w))]

end OriginalShearBoxBudget318
