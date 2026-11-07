module
public import ContactCurvature318
public import FiveContactMetricBounds318
public section
noncomputable section
open Finset DistanceLaplacian318 ContactCurvature318 FiniteLaplacian318
namespace GradientNorm318
set_option maxHeartbeats 0
variable {ι:Type*} [Fintype ι]

@[expose] def direction (x y:ℝ) : ℂ := ⟨x/radius x y,y/radius x y⟩

theorem direction_norm (x y:ℝ) (h:0<x^2+y^2) : ‖direction x y‖=1 := by
  have hs:‖direction x y‖^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp only [direction]
    have hr:radius x y≠0:=(radius_pos h).ne'
    field_simp
    nlinarith [radius_sq x y]
  nlinarith [norm_nonneg (direction x y)]

theorem sum_gradient_bound (x y:Fin 4→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    (∑i,x i/radius (x i) (y i))^2+(∑i,y i/radius (x i) (y i))^2≤16 := by
  have hn:‖∑i:Fin 4,direction (x i) (y i)‖≤4 := by
    calc
      _ ≤ ∑i:Fin 4,‖direction (x i) (y i)‖ := norm_sum_le _ _
      _ = 4 := by simp_rw [direction_norm _ _ (h _)];norm_num
  have hs:=Complex.sq_norm (∑i:Fin 4,direction (x i) (y i))
  have hn0 := norm_nonneg (∑i:Fin 4,direction (x i) (y i))
  simp only [Complex.normSq_apply,Complex.re_sum,Complex.im_sum,direction] at hs
  dsimp only [direction] at hn hn0
  nlinarith [sq_nonneg (4-‖∑i:Fin 4,(⟨x i/radius (x i) (y i),y i/radius (x i) (y i)⟩:ℂ)‖)]

theorem total_deriv_x (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    deriv (fun t:ℝ=>total x y (t,0)) 0=∑i,x i/radius (x i) (y i) := by
  have hd:= (HasDerivAt.sum (u:=Finset.univ)
    (fun i _=>hasDerivAt_line (x i) (y i) 0 (by simpa using h i))).const_add 1
  simpa only [total,translated,add_zero,Finset.sum_apply] using hd.deriv

theorem total_deriv_y (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    deriv (fun t:ℝ=>total x y (0,t)) 0=∑i,y i/radius (x i) (y i) := by
  have he:(fun t:ℝ=>total x y (0,t))=(fun t=>total y x (t,0)) := by
    funext t
    simp only [total,translated,add_zero]
    congr 1
    exact Finset.sum_congr rfl (fun i _=>radius_symm _ _)
  rw [he,total_deriv_x y x (fun i=>by nlinarith [h i])]
  exact Finset.sum_congr rfl (fun i _=>by rw [radius_symm (y i) (x i)])

theorem actual_gradient_bound (x y:Fin 4→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    gradientSq (total x y)≤16 := by
  rw [gradientSq,total_deriv_x x y h,total_deriv_y x y h]
  exact sum_gradient_bound x y h

/-- The actual computed curvature is bounded below by the four-distance
quotient, after the actual gradient and reciprocal inequalities. -/
theorem curvature_lower (x y:Fin 4→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    FiveContactMetricBounds318.tripleSum (radius (x 0) (y 0)) (radius (x 1) (y 1))
      (radius (x 2) (y 2)) (radius (x 3) (y 3))/(2*(total x y (0,0))^3) ≤
      -ConformalCurvature318.curvature (metric x y) := by
  have hg:=actual_gradient_bound x y h
  have hn:=FiveContactMetricBounds318.curvature_numerator
    (radius (x 0) (y 0)) (radius (x 1) (y 1)) (radius (x 2) (y 2)) (radius (x 3) (y 3))
    (gradientSq (total x y)) (radius_pos (h 0)) (radius_pos (h 1))
    (radius_pos (h 2)) (radius_pos (h 3)) hg
  have hn' : (∑i,(radius (x i) (y i))⁻¹)≤
      total x y (0,0)*(∑i,(radius (x i) (y i))⁻¹)-gradientSq (total x y) := by
    simpa [total,translated,Fin.sum_univ_four,one_div,add_assoc] using hn
  rw [negative_curvature x y h]
  have hp : 0≤(∏i,radius (x i) (y i))/(2*(total x y (0,0))^3) := by
    exact div_nonneg (Finset.prod_nonneg (fun i _=>(radius_pos (h i)).le))
      (by positivity [total_pos x y (0,0)])
  have hm:=mul_le_mul_of_nonneg_left hn' hp
  have he : (∏i,radius (x i) (y i))/(2*(total x y (0,0))^3)*
      (∑i,(radius (x i) (y i))⁻¹)=
      FiveContactMetricBounds318.tripleSum (radius (x 0) (y 0)) (radius (x 1) (y 1))
      (radius (x 2) (y 2)) (radius (x 3) (y 3))/(2*(total x y (0,0))^3) := by
    have h0:radius (x 0) (y 0)≠0:=(radius_pos (h 0)).ne'
    have h1:radius (x 1) (y 1)≠0:=(radius_pos (h 1)).ne'
    have h2:radius (x 2) (y 2)≠0:=(radius_pos (h 2)).ne'
    have h3:radius (x 3) (y 3)≠0:=(radius_pos (h 3)).ne'
    simp only [Fin.sum_univ_four,Fin.prod_univ_four,FiveContactMetricBounds318.tripleSum]
    field_simp
    ring
  rwa [he] at hm

end GradientNorm318
#print axioms GradientNorm318.actual_gradient_bound
#print axioms GradientNorm318.curvature_lower
