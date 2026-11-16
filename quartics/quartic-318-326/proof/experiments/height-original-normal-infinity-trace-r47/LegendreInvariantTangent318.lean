module
public import LegendreLiteralCompletedAtlas318
public import ShortInfinityDifferential318
public section
noncomputable section
namespace LegendreInvariantTangent318
open LegendreIndependentGraphs318 NormalizedLegendreProjectiveModel318
open LegendreFiniteComplexAtlas318 LegendrePlaneOverlap318
attribute [local instance] Classical.propDecidable

@[expose] def finiteSlope (l x : ℂ) : ℂ := 3*x^2+A l
@[expose] def J (l u v : ℂ) : ℂ := 1-2*A l*u*v-3*B l*v^2
@[expose] def H (l u v : ℂ) : ℂ := 3*u^2+A l*v^2
/-- Evaluation of the invariant differential on an actual plane tangent.
The alternate formula retains all finite branch points. -/
@[expose] def finiteValue (l x y dx dy : ℂ) : ℂ :=
  if 2*y≠0 then dx/(2*y) else dy/finiteSlope l x
/-- The minus sign is forced by the ACTUAL native infinity overlap. -/
@[expose] def infinityValue (l u v du dv : ℂ) : ℂ :=
  if J l u v≠0 then -du/J l u v else -dv/H l u v

lemma finite_x_formula (l x y dx dy : ℂ) (hy : 2*y≠0) :
    finiteValue l x y dx dy=dx/(2*y) := by simp only [finiteValue,if_pos hy]
lemma finite_y_formula (l x y dx dy : ℂ) (hx : finiteSlope l x≠0)
    (ht : finiteSlope l x*dx=2*y*dy) :
    finiteValue l x y dx dy=dy/finiteSlope l x := by
  by_cases hy : 2*y≠0
  · rw [finite_x_formula _ _ _ _ _ hy]
    field_simp [hx,hy]
    linear_combination ht
  · simp only [finiteValue,if_neg hy]
lemma infinity_u_formula (l u v du dv : ℂ) (hj : J l u v≠0) :
    infinityValue l u v du dv= -du/J l u v := by
  simp only [infinityValue,if_pos hj]
lemma infinity_v_formula (l u v du dv : ℂ) (hh : H l u v≠0)
    (ht : J l u v*dv=H l u v*du) :
    infinityValue l u v du dv= -dv/H l u v := by
  by_cases hj : J l u v≠0
  · rw [infinity_u_formula _ _ _ _ _ hj]
    field_simp [hj,hh]
    linear_combination ht
  · simp only [infinityValue,if_neg hj]

variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
/-- No tangent direction is lost at the branch points: the value vanishes
if and only if the genuine equation-tangent vector vanishes. -/
theorem finite_kernel (p : Plane l) (dx dy : ℂ)
    (ht : finiteSlope l p.val.1*dx=2*p.val.2*dy) :
    finiteValue l p.val.1 p.val.2 dx dy=0 ↔ dx=0 ∧ dy=0 := by
  constructor
  · intro hz
    rcases finite_partial_nonzero l p.val p.property with hy|hx
    · rw [finite_x_formula _ _ _ _ _ hy] at hz
      have hdx : dx=0 := (div_eq_zero_iff).mp hz |>.resolve_right hy
      have hdy : dy=0 := by
        rw [hdx,mul_zero] at ht
        exact (mul_eq_zero.mp ht.symm).resolve_left hy
      exact ⟨hdx,hdy⟩
    · have hx' : finiteSlope l p.val.1≠0 := neg_ne_zero.mp hx
      rw [finite_y_formula _ _ _ _ _ hx' ht] at hz
      have hdy : dy=0 := (div_eq_zero_iff).mp hz |>.resolve_right hx'
      have hdx : dx=0 := by
        rw [hdy,mul_zero] at ht
        exact (mul_eq_zero.mp ht).resolve_left hx'
      exact ⟨hdx,hdy⟩
  · rintro ⟨rfl,rfl⟩
    simp [finiteValue]

theorem infinity_kernel (p : InfinityPlane l) (du dv : ℂ)
    (ht : J l p.val.1 p.val.2*dv=H l p.val.1 p.val.2*du) :
    infinityValue l p.val.1 p.val.2 du dv=0 ↔ du=0 ∧ dv=0 := by
  constructor
  · intro hz
    rcases LegendreInfinityIndependentGraphs318.partial_nonzero l p.val p.property with hj|hh
    · change J l p.val.1 p.val.2≠0 at hj
      rw [infinity_u_formula _ _ _ _ _ hj] at hz
      have hdu : du=0 := neg_eq_zero.mp ((div_eq_zero_iff).mp hz |>.resolve_right hj)
      have hdv : dv=0 := by
        rw [hdu,mul_zero] at ht
        exact (mul_eq_zero.mp ht).resolve_left hj
      exact ⟨hdu,hdv⟩
    · have hh' : H l p.val.1 p.val.2≠0 := neg_ne_zero.mp hh
      rw [infinity_v_formula _ _ _ _ _ hh' ht] at hz
      have hdv : dv=0 := neg_eq_zero.mp ((div_eq_zero_iff).mp hz |>.resolve_right hh')
      have hdu : du=0 := by
        rw [hdv,mul_zero] at ht
        exact (mul_eq_zero.mp ht.symm).resolve_left hh'
      exact ⟨hdu,hdv⟩
  · rintro ⟨rfl,rfl⟩
    simp [infinityValue]

/-- At the ACTUAL infinity origin the invariant coefficient in the native
U coordinate is -1, not a pole or a vanishing form. -/
lemma infinity_origin (du dv : ℂ) : infinityValue l 0 0 du dv= -du := by
  simp [infinityValue,J]

/-- Full genuine overlap on equation-tangent vectors. This is the
Jacobian of (U,V)↦(x,y)=(U/V,1/V), with no arbitrary frame rescaling. -/
theorem actual_overlap (p : InfinityPlane l) (hv : p.val.2≠0) (du dv : ℂ)
    (ht : J l p.val.1 p.val.2*dv=H l p.val.1 p.val.2*du) :
    finiteValue l (p.val.1/p.val.2) (1/p.val.2)
      ((du*p.val.2-p.val.1*dv)/p.val.2^2) (-dv/p.val.2^2)=
        infinityValue l p.val.1 p.val.2 du dv := by
  have hscalar : p.val.2*J l p.val.1 p.val.2-p.val.1*H l p.val.1 p.val.2= -2*p.val.2 :=
    ShortInfinityDifferential318.scalar_identity (A l) (B l) p.val.1 p.val.2 p.property
  let w : ℂ := (p.val.2*du-p.val.1*dv)/(2*p.val.2)
  have hjw : J l p.val.1 p.val.2*w= -du := by
    have he : J l p.val.1 p.val.2*(p.val.2*du-p.val.1*dv)= -2*p.val.2*du := by
      linear_combination du*hscalar-p.val.1*ht
    dsimp [w]
    field_simp [hv]
    linear_combination he
  have hhw : H l p.val.1 p.val.2*w= -dv := by
    have he : H l p.val.1 p.val.2*(p.val.2*du-p.val.1*dv)= -2*p.val.2*dv := by
      linear_combination dv*hscalar-p.val.2*ht
    dsimp [w]
    field_simp [hv]
    linear_combination he
  have hy : (2:ℂ)*(1/p.val.2)≠0 := mul_ne_zero (by norm_num) (div_ne_zero one_ne_zero hv)
  rw [finite_x_formula _ _ _ _ _ hy]
  have he : ((du*p.val.2-p.val.1*dv)/p.val.2^2)/(2*(1/p.val.2))=w := by
    dsimp [w]
    field_simp [hv]
    <;> ring
  rw [he]
  by_cases hj : J l p.val.1 p.val.2≠0
  · rw [infinity_u_formula _ _ _ _ _ hj]
    exact (eq_div_iff hj).mpr (by simpa only [mul_comm] using hjw)
  · have hh : H l p.val.1 p.val.2≠0 := by
      rcases LegendreInfinityIndependentGraphs318.partial_nonzero l p.val p.property with hj'|hh'
      · exact (hj hj').elim
      · exact neg_ne_zero.mp hh'
    rw [infinity_v_formula _ _ _ _ _ hh ht]
    exact (eq_div_iff hh).mpr (by simpa only [mul_comm] using hhw)
end LegendreInvariantTangent318
