module
public import OriginalReducedCoefficientHeight318
public section
noncomputable section
namespace OriginalReducedDegreeBounds318
open MvPolynomial LiteralSievePolynomial318 TernaryQuadraticLineCover318
open OriginalReducedPolynomialEquiv318
set_option maxHeartbeats 4000000

lemma add_bound (f g : Poly) (n : ℕ) (hf : f.totalDegree≤n) (hg : g.totalDegree≤n) :
    (f+g).totalDegree≤n := (totalDegree_add f g).trans (max_le hf hg)
lemma mul_bound (f g : Poly) (m n : ℕ) (hf : f.totalDegree≤m) (hg : g.totalDegree≤n) :
    (f*g).totalDegree≤m+n := (totalDegree_mul f g).trans (Nat.add_le_add hf hg)
lemma scaled_bound (a : ℚ) (f : Poly) (n : ℕ) (hf : f.totalDegree≤n) :
    (C a*f).totalDegree≤n := by
  have hh := mul_bound (C a) f 0 n (by simp) hf
  simpa only [zero_add] using hh
lemma square_bound (f : Poly) (n : ℕ) (hf : f.totalDegree≤n) :
    (f^2).totalDegree≤2*n := (totalDegree_pow f 2).trans (Nat.mul_le_mul_left 2 hf)
lemma linear_bound (a : Vector ℚ) : (linear a).totalDegree≤1 := by
  apply add_bound
  · apply add_bound
    · exact scaled_bound a.1 (X 0) 1 (by simp)
    · exact scaled_bound a.2.1 (X 1) 1 (by simp)
  · exact scaled_bound a.2.2 (X 2) 1 (by simp)
lemma variable_bound (u v z : Vector ℚ) (i : Fin 3) : (variables u v z i).totalDegree≤1 := by
  fin_cases i
  · simpa [variables] using linear_bound (u.1,v.1,z.1)
  · simpa [variables] using linear_bound (u.2.1,v.2.1,z.2.1)
  · simpa [variables] using linear_bound (u.2.2,v.2.2,z.2.2)

/-- Absolute degree budgets survive the ACTUAL reduced substitution:
the two coprime constraint polynomials remain degree<=2 and the product
and norm polynomials degree<=4. Zero or cancellation only lowers degree. -/
theorem original_reduced_degrees (κ t : ℚ) (u v z : Vector ℚ) :
    (forward u v z (firstP κ t)).totalDegree≤2 ∧
    (forward u v z (secondP κ t)).totalDegree≤2 ∧
    (forward u v z (productD t)).totalDegree≤4 ∧
    (forward u v z (normK κ t)).totalDegree≤4 := by
  let x := variables u v z 0
  let y := variables u v z 1
  let w := variables u v z 2
  have hx : x.totalDegree≤1 := variable_bound u v z 0
  have hy : y.totalDegree≤1 := variable_bound u v z 1
  have hw : w.totalDegree≤1 := variable_bound u v z 2
  have hx2 : (x^2).totalDegree≤2 := square_bound x 1 hx
  have hy2 : (y^2).totalDegree≤2 := square_bound y 1 hy
  have hw2 : (w^2).totalDegree≤2 := square_bound w 1 hw
  have hxy : (x*y).totalDegree≤2 := mul_bound x y 1 1 hx hy
  have hκ : (C κ*w^2).totalDegree≤2 := scaled_bound κ (w^2) 2 hw2
  have hminus : (C (-1)*(x*y)).totalDegree≤2 := scaled_bound (-1) (x*y) 2 hxy
  have hcore : (C κ*w^2+C (-1)*(x*y)+C (t^2+2*t)).totalDegree≤2 :=
    add_bound _ _ 2 (add_bound _ _ 2 hκ hminus) (by simp)
  have hsum : (x+y).totalDegree≤1 := add_bound x y 1 hx hy
  have hK : ((C κ*w^2+C (-1)*(x*y)+C (t^2+2*t))^2+
      C (t^2)*(x+y)^2).totalDegree≤4 :=
    add_bound _ _ 4 (square_bound _ 2 hcore)
      (scaled_bound (t^2) _ 4 ((square_bound _ 1 hsum).trans (by norm_num)))
  refine ⟨?_,?_,?_,?_⟩
  · have he : forward u v z (firstP κ t)=C κ*w^2+C (2*t) := by
      simp [forward,firstP,w,algebraMap_eq]
    rw [he]
    exact add_bound _ _ 2 hκ (by simp)
  · have he : forward u v z (secondP κ t)=C (κ*(t+2))*w^2+C (-2)*(x*y) := by
      simp [forward,secondP,x,y,w,algebraMap_eq] <;> ring
    rw [he]
    exact add_bound _ _ 2 (scaled_bound _ _ 2 hw2) (scaled_bound _ _ 2 hxy)
  · have he : forward u v z (productD t)=(C (t^2)+x^2)*(C (t^2)+y^2) := by
      simp [forward,productD,x,y,algebraMap_eq]
    rw [he]
    exact mul_bound _ _ 2 2 (add_bound _ _ 2 (by simp) hx2) (add_bound _ _ 2 (by simp) hy2)
  · have he : forward u v z (normK κ t)=
        (C κ*w^2+C (-1)*(x*y)+C (t^2+2*t))^2+C (t^2)*(x+y)^2 := by
      simp [forward,normK,x,y,w,algebraMap_eq] <;> ring
    rw [he]
    exact hK

end OriginalReducedDegreeBounds318
