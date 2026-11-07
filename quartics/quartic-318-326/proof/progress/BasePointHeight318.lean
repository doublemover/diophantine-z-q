module
public import PrimitiveQuadraticMahler318
public section
noncomputable section
open NumberField ConcreteG8Domain LocalGenerator318 GlobalSaturationHeight318 ActualQuadraticEmbeddings318
namespace BasePointHeight318
set_option maxHeartbeats 0

lemma base_root_polynomial : (64:K)*xP^2+(-912:K)*xP+(1681:K)=0 := by
  ext <;> norm_num [xP,pair,pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

lemma base_real_roots_gt_one :
    1<(57:ℝ)/8+(-((7:ℝ)/2))*Real.sqrt 2 ∧
    1<(57:ℝ)/8-(-((7:ℝ)/2))*Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hu : Real.sqrt (2:ℝ)<3/2 := by nlinarith
  constructor <;> nlinarith

lemma relative_height_xP [NumberField K] : Height.mulHeight₁ xP=1681 := by
  have hf := PrimitiveQuadraticMahler318.finite_part_primitive 64 (-912) 1681 (57/8) (-7/2)
    (by norm_num) (by norm_num) (by norm_num) base_root_polynomial
  rw [NumberField.mulHeight₁_eq,xP,infinite_part_pair,hf]
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Nat.cast_ofNat]
  obtain ⟨h1,h2⟩ := base_real_roots_gt_one
  rw [abs_of_pos (lt_trans (by norm_num) h1),abs_of_pos (lt_trans (by norm_num) h2),
    max_eq_left h1.le,max_eq_left h2.le]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  nlinarith

lemma absolute_height_xP : NumberField.absLogHeight₁ xP=Real.log 41 := by
  let : NumberField K := {}
  rw [AbsoluteHeightNormalization318.absLogHeight_eq_half_relative,relative_height_xP]
  have hpow : (1681:ℝ)=41^2 := by norm_num
  rw [hpow,Real.log_pow]
  ring

lemma heightP : xHeight P=Real.log 41 := by
  simpa only [xHeight,P,WeierstrassCurve.Affine.Point.xRep_some,Matrix.cons_val_zero] using absolute_height_xP

#print axioms base_root_polynomial
#print axioms base_real_roots_gt_one
#print axioms relative_height_xP
#print axioms absolute_height_xP
#print axioms heightP
end BasePointHeight318
