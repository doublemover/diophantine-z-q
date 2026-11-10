module
public import ReflectedConvexDisk318
public section
noncomputable section
namespace PELMaximalHalfOctagonShape318
open Set Metric Filter
open scoped Topology
open ReflectedDiskJoukowski318
/-- Literal half of the exploratory full-normalizer octagon, centered at
(0,1/2) in complex coordinates. Arithmetic fundamental-domain identification
is a separate theorem; these geometric properties are unconditional. -/
@[expose] def centeredPolygon : Set ℂ := {z |
  -30≤z.re ∧ z.re≤30 ∧ -(1/2:ℝ)≤z.im ∧ z.im≤1/2 ∧
  z.re+7*z.im≤63/2 ∧ -z.re+7*z.im≤63/2}
@[expose] def strictPolygon : Set ℂ := {z |
  -30<z.re ∧ z.re<30 ∧ -(1/2:ℝ)<z.im ∧ z.im<1/2 ∧
  z.re+7*z.im<63/2 ∧ -z.re+7*z.im<63/2}

theorem polygon_reflected (z : ℂ) : reflected z∈centeredPolygon ↔ z∈centeredPolygon := by
  simp only [centeredPolygon,reflected,Set.mem_setOf_eq,Complex.neg_re,Complex.conj_re,
    Complex.neg_im,Complex.conj_im,neg_neg]
  constructor <;> rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem polygon_closed : IsClosed centeredPolygon := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le Complex.continuous_im continuous_const).inter
    ((isClosed_le (Complex.continuous_re.add (continuous_const.mul Complex.continuous_im))
      continuous_const).inter
    (isClosed_le (Complex.continuous_re.neg.add (continuous_const.mul Complex.continuous_im))
      continuous_const)))))

theorem strict_open : IsOpen strictPolygon := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
    ((isOpen_lt (Complex.continuous_re.add (continuous_const.mul Complex.continuous_im))
      continuous_const).inter
    (isOpen_lt (Complex.continuous_re.neg.add (continuous_const.mul Complex.continuous_im))
      continuous_const)))))

theorem polygon_zero_neighborhood : centeredPolygon∈𝓝 0 := by
  have hzero : (0:ℂ)∈strictPolygon := by norm_num [strictPolygon]
  apply Filter.mem_of_superset (strict_open.mem_nhds hzero)
  rintro z ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact ⟨h₁.le,h₂.le,h₃.le,h₄.le,h₅.le,h₆.le⟩

theorem polygon_convex : Convex ℝ centeredPolygon := by
  intro z hz w hw a b ha hb hab
  obtain ⟨z₁,z₂,z₃,z₄,z₅,z₆⟩ := hz
  obtain ⟨w₁,w₂,w₃,w₄,w₅,w₆⟩ := hw
  simp only [centeredPolygon,Set.mem_setOf_eq,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,smul_eq_mul]
  have H (c x y : ℝ) (hx : x≤c) (hy : y≤c) : a*x+b*y≤c := by
    have h₁ := mul_le_mul_of_nonneg_left hx ha
    have h₂ := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have h := H 30 (-z.re) (-w.re) (by linarith) (by linarith); nlinarith
  · exact H 30 z.re w.re z₂ w₂
  · have h := H (1/2) (-z.im) (-w.im) (by linarith) (by linarith); nlinarith
  · exact H (1/2) z.im w.im z₄ w₄
  · have h := H (63/2) (z.re+7*z.im) (w.re+7*w.im) z₅ w₅; nlinarith
  · have h := H (63/2) (-z.re+7*z.im) (-w.re+7*w.im) z₆ w₆; nlinarith

theorem polygon_bounded : Bornology.IsBounded centeredPolygon := by
  apply (isBounded_closedBall : Bornology.IsBounded (closedBall (0:ℂ) 31)).subset
  intro z hz
  obtain ⟨h₁,h₂,h₃,h₄,_,_⟩ := hz
  have hre : |z.re|≤30 := abs_le.mpr ⟨by linarith,h₂⟩
  have him : |z.im|≤1/2 := abs_le.mpr ⟨by linarith,h₄⟩
  have hn : ‖z‖≤|z.re|+|z.im| := by
    calc
      ‖z‖=‖(z.re:ℂ)+(z.im:ℂ)*Complex.I‖ := by rw [Complex.re_add_im]
      _≤‖(z.re:ℂ)‖+‖(z.im:ℂ)*Complex.I‖ := norm_add_le _ _
      _=|z.re|+|z.im| := by simp
  change dist z 0≤31
  rw [dist_zero_right]
  linarith

instance polygonCompact : CompactSpace centeredPolygon :=
  isCompact_iff_compactSpace.mp (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨polygon_closed,polygon_bounded⟩)

/-- Actual symmetry-preserving normalization, not an arbitrary selected
homeomorphism that might destroy the boundary reflection. -/
@[expose] def polygonDiskHomeomorph : centeredPolygon ≃ₜ Disk :=
  ReflectedConvexDisk318.closedDiskHomeomorph centeredPolygon polygon_convex
    polygon_zero_neighborhood polygon_bounded polygon_closed

theorem normalized_reflection (z : centeredPolygon) :
    (polygonDiskHomeomorph ⟨reflected z.val,(polygon_reflected z.val).mpr z.property⟩).val=
      reflected (polygonDiskHomeomorph z).val :=
  ReflectedConvexDisk318.normalization_reflected centeredPolygon polygon_convex
    polygon_zero_neighborhood polygon_bounded polygon_reflected z.val
end PELMaximalHalfOctagonShape318
