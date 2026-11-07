module
public import LucasHeight318
public import RationalHeight318
public section
namespace HeightSeparation318

/-- The complete numerical height/separation chain for the actual 318 exponents.
No source arithmetic or certificate-existence hypothesis is hidden here. The
remaining hypotheses are precisely the group/anchor, high and low contact-height,
scalar-height and Lucas-growth results that must be connected to raw witnesses. -/
theorem integer_input_from_height_and_group_data
    (q : ℚ) (n a t z : ℤ) (B c : ℝ)
    (hn : Odd n) (hB : 3 ≤ B)
    (hnB : |(n:ℝ)| ≤ B) (haB : |(a:ℝ)| ≤ B)
    (htB : |(t:ℝ)| ≤ B) (hzB : |(z:ℝ)| ≤ B)
    (horient : c=|(a:ℝ)-1| ∨ c=|(a:ℝ)+1|)
    (hanchor : 2*3^32767 ≤ c)
    (hhigh : lucasResidual a t z ≠ 0 → B^2-6 < 7*heightConstant*
      |lucasResidual a t z|^((49:ℝ)/104))
    (hlucas : lucasResidual a t z = 0 → |(a:ℝ)|-3 < Real.log B)
    (hscalar : ZInQ.rationalLogHeight (3723*(2*q+1)^2) ≤
      heightConstant*c^((49:ℝ)/64))
    (hlow : 3723*(2*q+1)^2 ≠ n → B^2-6 < 7*heightConstant*
      (((3723*(2*q+1)^2-n).num.natAbs:ℝ)^((49:ℝ)/32))) :
    ∃ x:ℤ,(x:ℚ)=q := by
  have hbinary := anchor_binary_bound c hanchor
  have hsize := (scalar_orientation_bounds a c horient).1
  have hcB : c≤B+1 := by linarith only [hsize, haB]
  have hzero := lucas_residual_zero a t z B c hB haB htB hzB hbinary hcB hhigh
  have hlog : c-4<Real.log B := by
    have hg := hlucas hzero
    linarith only [hsize, hg]
  have hc8 : 8≤c := by
    have hpow : (2:ℝ)^3≤2^49151 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num only [show (2:ℝ)^3=8 by norm_num] at hpow
    exact hpow.trans hbinary.le
  exact odd_input_integral q n B c hn hB hnB hbinary hc8 hscalar hlog hlow

end HeightSeparation318
