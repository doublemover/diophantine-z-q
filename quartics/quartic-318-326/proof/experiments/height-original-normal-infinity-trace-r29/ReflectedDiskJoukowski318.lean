module
public import SphereInversion318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace ReflectedDiskJoukowski318
open Set Metric Filter Topology
open scoped OnePoint ComplexConjugate
attribute [local instance] Classical.propDecidable
abbrev Disk := closedBall (0:ℂ) 1
@[expose] def reflected (z : ℂ) : ℂ := -conj z
@[expose] def joukowski (z : ℂ) : OnePoint ℂ :=
  if z=0 then ∞ else ((z-z⁻¹:ℂ):OnePoint ℂ)
@[expose] def diskMap (z : Disk) : OnePoint ℂ := joukowski z.val

theorem disk_bound (z : Disk) : ‖z.val‖≤1 := by
  simpa only [Metric.mem_closedBall,dist_zero_right] using z.property

theorem factor (z w : ℂ) (hz : z≠0) (hw : w≠0) :
    (z-w)*(z*w+1)=(z*w)*((z-z⁻¹)-(w-w⁻¹)) := by
  field_simp [hz,hw]
  <;> ring

theorem affine_fibers (z w : ℂ) (hz : z≠0) (hw : w≠0) :
    z-z⁻¹=w-w⁻¹ ↔ z=w ∨ z*w=-1 := by
  constructor
  · intro h
    have hf : (z-w)*(z*w+1)=0 := by rw [factor z w hz hw,h]; ring
    rcases mul_eq_zero.mp hf with h₁ | h₂
    · exact Or.inl (sub_eq_zero.mp h₁)
    · right; linear_combination h₂
  · rintro (rfl | h)
    · rfl
    · have hf : (z-w)*(z*w+1)=0 := by rw [h]; ring
      rw [factor z w hz hw] at hf
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (mul_ne_zero hz hw))

theorem sphere_fibers (z w : ℂ) : joukowski z=joukowski w ↔ z=w ∨ z*w=-1 := by
  by_cases hz : z=0
  · subst z
    by_cases hw : w=0
    · subst w; simp [joukowski]
    · simp [joukowski,hw,Ne.symm hw]
  · by_cases hw : w=0
    · subst w; simp [joukowski,hz]
    · simp only [joukowski,if_neg hz,if_neg hw]
      constructor
      · intro h; exact (affine_fibers z w hz hw).mp (OnePoint.coe_injective h)
      · intro h; exact congrArg (fun x : ℂ => (x:OnePoint ℂ)) ((affine_fibers z w hz hw).mpr h)

theorem norm_one_of_product (z w : Disk) (h : z.val*w.val=-1) : ‖z.val‖=1 ∧ ‖w.val‖=1 := by
  have hp : ‖z.val‖*‖w.val‖=1 := by simpa only [norm_mul,norm_neg,norm_one] using congrArg norm h
  have hz := disk_bound z
  have hw := disk_bound w
  have hzn := norm_nonneg z.val
  have hwn := norm_nonneg w.val
  have hle₁ := mul_le_mul_of_nonneg_left hw hzn
  have hle₂ := mul_le_mul_of_nonneg_right hz hwn
  constructor <;> nlinarith

theorem inverse_on_circle (z : ℂ) (hz : ‖z‖=1) : z⁻¹=conj z := by
  rw [Complex.inv_def,Complex.normSq_eq_norm_sq,hz]
  norm_num

theorem product_iff_boundary_reflection (z w : Disk) : z.val*w.val=-1 ↔
    ‖z.val‖=1 ∧ w.val=reflected z.val := by
  constructor
  · intro h
    have hn := (norm_one_of_product z w h).1
    have hz0 : z.val≠0 := by intro hz; rw [hz,norm_zero] at hn; norm_num at hn
    refine ⟨hn,?_⟩
    rw [reflected,←inverse_on_circle z.val hn]
    apply mul_left_cancel₀ hz0
    rw [h,mul_neg,mul_inv_cancel₀ hz0]
  · rintro ⟨hn,hw⟩
    have hz0 : z.val≠0 := by intro hz; rw [hz,norm_zero] at hn; norm_num at hn
    rw [hw,reflected,←inverse_on_circle z.val hn,mul_neg,mul_inv_cancel₀ hz0]

/-- Complete boundary-reflection relation of the ACTUAL disk map. Interior
points have singleton fibers; the second alternative is exactly reflection
across the imaginary axis on the unit circle. -/
theorem diskMap_fibers (z w : Disk) : diskMap z=diskMap w ↔
    z=w ∨ (‖z.val‖=1 ∧ w.val=reflected z.val) := by
  change joukowski z.val=joukowski w.val ↔ _
  rw [sphere_fibers,product_iff_boundary_reflection]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem quadratic_root_in_disk (w : ℂ) : ∃ z : ℂ, ‖z‖≤1 ∧ z≠0 ∧ z-z⁻¹=w := by
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (w^2+4) (show 0<2 by decide)
  let a : ℂ := (w+d)/2
  let b : ℂ := (w-d)/2
  have ha : a^2-w*a-1=0 := by dsimp [a]; linear_combination (1/4:ℂ)*hd
  have hb : b^2-w*b-1=0 := by dsimp [b]; linear_combination (1/4:ℂ)*hd
  have hab : a*b=-1 := by dsimp [a,b]; linear_combination -(1/4:ℂ)*hd
  have ha0 : a≠0 := by intro h; rw [h,zero_mul] at hab; norm_num at hab
  have hb0 : b≠0 := by intro h; rw [h,mul_zero] at hab; norm_num at hab
  have hp : ‖a‖*‖b‖=1 := by simpa only [norm_mul,norm_neg,norm_one] using congrArg norm hab
  have root_value (z : ℂ) (hz : z≠0) (hq : z^2-w*z-1=0) : z-z⁻¹=w := by
    have he : z^2-1=w*z := by linear_combination hq
    calc
      z-z⁻¹=(z^2-1)/z := by field_simp [hz] <;> ring
      _=w := (div_eq_iff hz).mpr he
  by_cases hna : ‖a‖≤1
  · exact ⟨a,hna,ha0,root_value a ha0 ha⟩
  · have hnb : ‖b‖≤1 := by
      have hna' := lt_of_not_ge hna
      by_contra hnb
      have hnb' : 1<‖b‖ := lt_of_not_ge hnb
      have hlt := mul_lt_mul_of_pos_left hna' (lt_trans zero_lt_one hnb')
      nlinarith
    exact ⟨b,hnb,hb0,root_value b hb0 hb⟩

theorem diskMap_surjective : Function.Surjective diskMap := by
  intro w
  induction w using OnePoint.rec with
  | infty => exact ⟨⟨0,by simp⟩,by simp [diskMap,joukowski]⟩
  | coe w =>
    obtain ⟨z,hz,hz0,hzw⟩ := quadratic_root_in_disk w
    refine ⟨⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz⟩,?_⟩
    simp only [diskMap,joukowski,if_neg hz0,hzw]
end ReflectedDiskJoukowski318
