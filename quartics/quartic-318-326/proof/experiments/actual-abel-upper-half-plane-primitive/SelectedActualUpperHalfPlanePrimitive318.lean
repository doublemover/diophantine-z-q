module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

public section

noncomputable section

open Filter Metric Set UpperHalfPlane
open scoped Topology

namespace SelectedActualUpperHalfPlanePrimitive318

private def height (n : ℕ) : ℝ := n + 1
private def center (n : ℕ) : ℂ := (height n : ℂ) * Complex.I
private def disk (n : ℕ) : Set ℂ := ball (center n) (height n)

private theorem height_pos (n : ℕ) : 0 < height n := by unfold height; positivity

private theorem disk_iff (n : ℕ) (z : ℂ) :
    z ∈ disk n ↔ Complex.normSq z < 2 * height n * z.im := by
  have he : ‖z - center n‖ ^ 2 =
      Complex.normSq z - 2 * height n * z.im + height n ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [center,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    ring
  have h := height_pos n
  have hnorm : 0 ≤ ‖z - center n‖ := norm_nonneg _
  have hs : 0 < height n + ‖z - center n‖ := add_pos_of_pos_of_nonneg h hnorm
  change dist z (center n) < height n ↔ _
  rw [dist_eq_norm]
  constructor
  · intro hz
    have hm := mul_pos (sub_pos.mpr hz) hs
    nlinarith only [hm,he]
  · intro hz
    by_contra! hc
    have hm := mul_nonneg (sub_nonneg.mpr hc) hs.le
    nlinarith only [hm,he,hz]

private theorem disk_subset (n : ℕ) : disk n ⊆ upperHalfPlaneSet := by
  intro z hz
  have he := (disk_iff n z).mp hz
  change 0 < z.im
  by_contra! h
  have hh := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (height_pos n).le) h
  exact (not_lt_of_ge (hh.trans (Complex.normSq_nonneg z))) he

private theorem disk_mono : Monotone disk := by
  intro n m hnm z hz
  have hp : 0 < z.im := disk_subset n hz
  have h : height n ≤ height m := by unfold height; exact add_le_add_right (by exact_mod_cast hnm) 1
  apply (disk_iff m z).mpr
  exact ((disk_iff n z).mp hz).trans_le
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) hp.le)

private theorem I_mem_disk (n : ℕ) : Complex.I ∈ disk n := by
  apply (disk_iff n Complex.I).mpr
  simp only [Complex.normSq_apply,Complex.I_re,Complex.I_im,mul_one]
  unfold height
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

private theorem exists_disk (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : ∃ n, z ∈ disk n := by
  have hp : 0 < 2 * z.im := mul_pos (by norm_num) hz
  obtain ⟨n,hn⟩ := exists_nat_gt (Complex.normSq z / (2 * z.im))
  have hlt : Complex.normSq z < (n : ℝ) * (2 * z.im) := (div_lt_iff₀ hp).mp hn
  refine ⟨n,(disk_iff n z).mpr ?_⟩
  unfold height
  nlinarith only [hlt,show 0 < z.im from hz]

/-- Global primitive on the literal upper half-plane.
The increasing tangent disks exhaust it; use the exact primitive on
each disk and use uniqueness after normalizing all of them at I.
No global primitive or simply-connected integration theorem is supplied. -/
theorem exists_normalized_primitive {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (f : ℂ → F)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) :
    ∃ P : ℂ → F, P Complex.I = 0 ∧
      ∀ z ∈ upperHalfPlaneSet, HasDerivAt P (f z) z := by
  classical
  have hex (n : ℕ) : ∃ P : ℂ → F, P Complex.I = 0 ∧
      ∀ z ∈ disk n, HasDerivAt P (f z) z :=
    (hf.mono (disk_subset n)).isExactOn_ball.with_val_at Complex.I 0
  choose P hPI hP using hex
  have hov (n m : ℕ) (hnm : n ≤ m) : (disk n).EqOn (P n) (P m) := by
    apply (isOpen_ball : IsOpen (disk n)).eqOn_of_fderiv_eq
      (convex_ball (center n) (height n)).isPreconnected
    · exact fun z hz => (hP n z hz).differentiableAt.differentiableWithinAt
    · exact fun z hz => (hP m z (disk_mono hnm hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      exact (hP n z hz).hasFDerivAt.fderiv.trans
        ((hP m z (disk_mono hnm hz)).hasFDerivAt.fderiv).symm
    · exact I_mem_disk n
    · exact (hPI n).trans (hPI m).symm
  let Q (z : ℂ) : F := if h : z ∈ upperHalfPlaneSet then P (Classical.choose (exists_disk z h)) z else 0
  have hQ (n : ℕ) : (disk n).EqOn Q (P n) := by
    intro z hz
    have hu := disk_subset n hz
    let m := Classical.choose (exists_disk z hu)
    have hm : z ∈ disk m := Classical.choose_spec (exists_disk z hu)
    change (if h : z ∈ upperHalfPlaneSet then P (Classical.choose (exists_disk z h)) z else 0) =
      P n z
    rw [dif_pos hu]
    exact (le_total m n).elim (fun h => hov m n h hm) (fun h => (hov n m h hz).symm)
  refine ⟨Q,(hQ 0 (I_mem_disk 0)).trans (hPI 0),?_⟩
  intro z hz
  obtain ⟨n,hn⟩ := exists_disk z hz
  have he : Q =ᶠ[𝓝 z] P n :=
    ((isOpen_ball : IsOpen (disk n)).eventually_mem hn).mono fun w hw => hQ n hw
  exact (hP n z hn).congr_of_eventuallyEq he

end SelectedActualUpperHalfPlanePrimitive318

#print axioms SelectedActualUpperHalfPlanePrimitive318.exists_normalized_primitive
