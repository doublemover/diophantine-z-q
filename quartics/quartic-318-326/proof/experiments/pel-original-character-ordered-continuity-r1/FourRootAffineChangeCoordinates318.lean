module
public import FourRootNormalizedPointCharts318
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace FourRootAffineChangeCoordinates318
open FourRootNormalizedPointCharts318
variable (b c : Fin 4 → ℂ) (d r : ℂ) (hr : r ≠ 0)
  (h : ∀ i, c i = d + r^2 * b i)

/-- The same four marked roots are multiplied by r. No root choices or
permutation of the branch labels enters this coordinate change. -/
@[expose] def finiteForward (p : FinitePoints b) : FinitePoints c :=
  ⟨(d+r^2*p.val.1,fun i => r*p.val.2 i),by
    intro i
    rw [mul_pow,p.property i,h i]
    ring⟩
@[expose] def finiteBackward (q : FinitePoints c) : FinitePoints b :=
  ⟨((q.val.1-d)/r^2,fun i => q.val.2 i/r),by
    intro i
    rw [div_pow,q.property i,h i]
    field_simp [hr]
    <;> ring⟩
lemma finite_left (p : FinitePoints b) :
    finiteBackward b c d r hr h (finiteForward b c d r h p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change (d+r^2*p.val.1-d)/r^2=p.val.1
    field_simp [hr]
    <;> ring
  · funext i
    change r*p.val.2 i/r=p.val.2 i
    field_simp [hr]
lemma finite_right (q : FinitePoints c) :
    finiteForward b c d r h (finiteBackward b c d r hr h q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · change d+r^2*((q.val.1-d)/r^2)=q.val.1
    field_simp [hr]
    <;> ring
  · funext i
    change r*(q.val.2 i/r)=q.val.2 i
    field_simp [hr]

/-- Normalized infinity retains ALL three independent sign ratios.
Its true coordinate is u/r, not u or a collapsed product of roots. -/
@[expose] def infinityForward (p : InfinityPoints b) : InfinityPoints c :=
  ⟨(p.val.1/r,p.val.2),p.property.1,by
    intro i
    rw [p.property.2 i,h 0,h i]
    field_simp [hr]
    <;> ring⟩
@[expose] def infinityBackward (q : InfinityPoints c) : InfinityPoints b :=
  ⟨(q.val.1*r,q.val.2),q.property.1,by
    intro i
    rw [q.property.2 i,h 0,h i]
    ring⟩
lemma infinity_left (p : InfinityPoints b) :
    infinityBackward b c d r h (infinityForward b c d r hr h p)=p := by
  apply Subtype.ext
  apply Prod.ext
  · change p.val.1/r*r=p.val.1
    exact div_mul_cancel₀ _ hr
  · rfl
lemma infinity_right (q : InfinityPoints c) :
    infinityForward b c d r hr h (infinityBackward b c d r h q)=q := by
  apply Subtype.ext
  apply Prod.ext
  · change q.val.1*r/r=q.val.1
    exact mul_div_cancel_right₀ _ hr
  · rfl

@[expose] def finiteEquiv : FinitePoints b ≃ₜ FinitePoints c where
  toFun := finiteForward b c d r h
  invFun := finiteBackward b c d r hr h
  left_inv := finite_left b c d r hr h
  right_inv := finite_right b c d r hr h
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.add (continuous_const.mul (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_pi (fun i => continuous_const.mul
        ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp continuous_subtype_val).sub continuous_const |>.div_const _).prodMk
      (continuous_pi (fun i => ((continuous_apply i).comp
        (continuous_snd.comp continuous_subtype_val)).div_const _))
@[expose] def infinityEquiv : InfinityPoints b ≃ₜ InfinityPoints c where
  toFun := infinityForward b c d r hr h
  invFun := infinityBackward b c d r h
  left_inv := infinity_left b c d r hr h
  right_inv := infinity_right b c d r hr h
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp continuous_subtype_val).div_const _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp continuous_subtype_val).mul continuous_const).prodMk
      (continuous_snd.comp continuous_subtype_val)
end FourRootAffineChangeCoordinates318
