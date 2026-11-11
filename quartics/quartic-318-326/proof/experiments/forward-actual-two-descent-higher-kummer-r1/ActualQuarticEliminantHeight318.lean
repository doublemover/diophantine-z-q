module
public import ActualQuarticRectangleTail318
public section
noncomputable section
namespace ActualQuarticEliminantHeight318
open ActualQuadraticQuarticEliminant318
set_option maxHeartbeats 9000000

lemma remainder_bounds (a b c e f g h i H : ℝ) (hH : 0≤H)
    (ha : |a|≤H) (hb : |b|≤H) (hc : |c|≤H) (he : |e|≤H)
    (hf : |f|≤H) (hg : |g|≤H) (hh : |h|≤H) (hi : |i|≤H) :
    |linearTerm a b c e f g h i|≤7*H^4 ∧ |constantTerm a b c e f g h i|≤5*H^4 := by
  have hb3 : |-b^3+2*a*b*c|≤3*H^3 := by
    calc
      _ ≤ |b|^3+2*|a|*|b|*|c| := by simpa [abs_mul,abs_pow] using abs_add (-b^3) (2*a*b*c)
      _ ≤ H^3+2*H*H*H := by gcongr
      _ = _ := by ring
  have hb2 : |b^2-a*c|≤2*H^2 := by
    calc
      _ ≤ |b|^2+|a|*|c| := by simpa [abs_mul,abs_pow] using abs_sub (b^2) (a*c)
      _ ≤ H^2+H*H := by gcongr
      _ = _ := by ring
  have hbc : |-b^2*c+a*c^2|≤2*H^3 := by
    calc
      _ ≤ |b|^2*|c|+|a|*|c|^2 := by simpa [abs_mul,abs_pow] using abs_add (-b^2*c) (a*c^2)
      _ ≤ H^2*H+H*H^2 := by gcongr
      _ = _ := by ring
  have L1 : |e*(-b^3+2*a*b*c)|≤3*H^4 := by
    rw [abs_mul]
    calc
      _ ≤ H*(3*H^3) := mul_le_mul he hb3 (abs_nonneg _) hH
      _ = _ := by ring
  have L2 : |f*a*(b^2-a*c)|≤2*H^4 := by
    simp only [abs_mul]
    calc
      _ ≤ H*H*(2*H^2) := by gcongr
      _ = _ := by ring
  have L3 : |g*a^2*b|≤H^4 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*H^2*H := by gcongr
      _ = _ := by ring
  have L4 : |h*a^3|≤H^4 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*H^3 := by gcongr
      _ = _ := by ring
  have M1 : |e*(-b^2*c+a*c^2)|≤2*H^4 := by
    rw [abs_mul]
    calc
      _ ≤ H*(2*H^3) := mul_le_mul he hbc (abs_nonneg _) hH
      _ = _ := by ring
  have M2 : |f*a*b*c|≤H^4 := by
    simp only [abs_mul]
    calc
      _ ≤ H*H*H*H := by gcongr
      _ = _ := by ring
  have M3 : |g*a^2*c|≤H^4 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*H^2*H := by gcongr
      _ = _ := by ring
  have M4 : |i*a^3|≤H^4 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*H^3 := by gcongr
      _ = _ := by ring
  have four (x y z w : ℝ) : |x+y-z+w|≤|x|+|y|+|z|+|w| := by
    have h1 := abs_add (x+y-z) w
    have h2 := abs_sub (x+y) z
    have h3 := abs_add x y
    linarith only [h1,h2,h3]
  constructor
  · have hz := four (e*(-b^3+2*a*b*c)) (f*a*(b^2-a*c)) (g*a^2*b) (h*a^3)
    dsimp [linearTerm]
    linarith only [hz,L1,L2,L3,L4]
  · have hz := four (e*(-b^2*c+a*c^2)) (f*a*b*c) (g*a^2*c) (i*a^3)
    dsimp [constantTerm]
    linarith only [hz,M1,M2,M3,M4]

/-- Explicit polynomial-size bound for the TRUE quartic pseudo-resultant.
The coefficient bound concerns all eight original coefficients, not values
of a rescaled or sampled polynomial. -/
theorem real_bound (a b c e f g h i H : ℝ) (hH : 0≤H)
    (ha : |a|≤H) (hb : |b|≤H) (hc : |c|≤H) (he : |e|≤H)
    (hf : |f|≤H) (hg : |g|≤H) (hh : |h|≤H) (hi : |i|≤H) :
    |eliminant a b c e f g h i|≤109*H^9 := by
  obtain ⟨hL,hM⟩ := remainder_bounds a b c e f g h i H hH ha hb hc he hf hg hh hi
  let L := linearTerm a b c e f g h i
  let M := constantTerm a b c e f g h i
  have hm1 : |a*M^2|≤25*H^9 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*(5*H^4)^2 := by gcongr
      _ = _ := by ring
  have hm2 : |b*L*M|≤35*H^9 := by
    simp only [abs_mul]
    calc
      _ ≤ H*(7*H^4)*(5*H^4) := by gcongr
      _ = _ := by ring
  have hm3 : |c*L^2|≤49*H^9 := by
    simp only [abs_mul,abs_pow]
    calc
      _ ≤ H*(7*H^4)^2 := by gcongr
      _ = _ := by ring
  have h1 := abs_add (a*M^2-b*L*M) (c*L^2)
  have h2 := abs_sub (a*M^2) (b*L*M)
  change |a*M^2-b*L*M+c*L^2|≤109*H^9
  linarith only [h1,h2,hm1,hm2,hm3]

theorem integer_bound (a b c e f g h i : ℤ) (H : ℝ) (hH : 0≤H)
    (ha : |(a:ℝ)|≤H) (hb : |(b:ℝ)|≤H) (hc : |(c:ℝ)|≤H) (he : |(e:ℝ)|≤H)
    (hf : |(f:ℝ)|≤H) (hg : |(g:ℝ)|≤H) (hh : |(h:ℝ)|≤H) (hi : |(i:ℝ)|≤H) :
    |(eliminant a b c e f g h i:ℝ)|≤109*H^9 := by
  have hz := real_bound (a:ℝ) b c e f g h i H hH ha hb hc he hf hg hh hi
  simpa only [eliminant,linearTerm,constantTerm,Int.cast_add,Int.cast_sub,Int.cast_mul,
    Int.cast_pow,Int.cast_neg,Int.cast_ofNat] using hz

end ActualQuarticEliminantHeight318
