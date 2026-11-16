module
public import ActualGaussianFullSourceTail318
public section
noncomputable section
namespace ActualGaussianExceptionalGrowth318
open ActualDivisorSubpower318 ActualGaussianZeroStratum318 ActualOriginalLevelSource318
set_option maxHeartbeats 14000000

@[expose] def zeroConstant (κ : ℤ) (δ : ℝ) : ℝ :=
  60*divisorConstant δ*(4*|(κ:ℝ)|)^δ+120
@[expose] def valueConstant (κ : ℤ) (δ : ℝ) : ℝ :=
  20*(divisorConstant δ)^2*(4:ℝ)^δ*(4*(|(κ:ℝ)|+1))^δ+
    40*divisorConstant δ*(4:ℝ)^δ

lemma scaled_square_rpow (c : ℝ) (hc : 0≤c) (B : ℕ) (δ : ℝ) :
    (c*(B:ℝ)^2)^δ=c^δ*(B:ℝ)^(2*δ) := by
  rw [Real.mul_rpow hc (sq_nonneg _),←Real.rpow_natCast_mul (by positivity : (0:ℝ)≤B) 2 δ]

lemma small_power_one (B : ℕ) (hB : 1≤B) (δ : ℝ) (hδ : 0<δ) :
    1≤(B:ℝ)^(2*δ) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hb (by positivity : 0≤2*δ)

lemma zero_growth (B : ℕ) (hB : 1≤B) (κ : ℤ) (δ : ℝ) (hδ : 0<δ) :
    zeroBudget B κ δ≤zeroConstant κ δ*(B:ℝ)^(2+2*δ) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hD := divisorConstant_pos δ hδ
  let P := (B:ℝ)^(2*δ)
  let X := (4*|(κ:ℝ)|)^δ
  have hP : 1≤P := small_power_one B hB δ hδ
  have hX : 0≤X := Real.rpow_nonneg (by positivity) _
  have hpow : (|(κ:ℝ)|*(2*(B:ℝ))^2)^δ=X*P := by
    have he : |(κ:ℝ)|*(2*(B:ℝ))^2=(4*|(κ:ℝ)|)*(B:ℝ)^2 := by ring
    rw [he,scaled_square_rpow _ (by positivity)]
  have hwidth : 4*(B:ℝ)+1≤5*(B:ℝ) := by linarith
  have houter : 2*(2*(B:ℝ)+1)≤6*(B:ℝ) := by linarith
  have hinner : (4*(B:ℝ)+1)*(2*divisorConstant δ*X*P)+4*(4*(B:ℝ)+1)≤
      5*(B:ℝ)*(2*divisorConstant δ*X*P)+20*(B:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hwidth (by positivity : 0≤2*divisorConstant δ*X*P)
    nlinarith only [hm,hwidth]
  have hm := mul_le_mul houter hinner (by positivity) (by positivity)
  have hsave := mul_le_mul_of_nonneg_left hP (by positivity : 0≤120*(B:ℝ)^2)
  have he : (B:ℝ)^2*P=(B:ℝ)^(2+2*δ) := by
    rw [Real.rpow_add hbpos,Real.rpow_two]
  rw [zeroBudget,hpow]
  rw [←he]
  dsimp [zeroConstant,X] at *
  nlinarith only [hm,hsave]

lemma value_growth (B : ℕ) (hB : 1≤B) (κ : ℤ) (δ : ℝ) (hδ : 0<δ) :
    valueBudget B κ δ≤valueConstant κ δ*(B:ℝ)^(1+4*δ) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hD := divisorConstant_pos δ hδ
  let P := (B:ℝ)^(2*δ)
  let X := (4:ℝ)^δ
  let Z := (4*(|(κ:ℝ)|+1))^δ
  have hP : 1≤P := small_power_one B hB δ hδ
  have hX : 0≤X := Real.rpow_nonneg (by norm_num) _
  have hZ : 0≤Z := Real.rpow_nonneg (by positivity) _
  have hwidth : 4*(B:ℝ)+1≤5*(B:ℝ) := by linarith
  have hinner : (4*(B:ℝ)+1)*(2*divisorConstant δ*Z*P)+4*(4*(B:ℝ)+1)≤
      5*(B:ℝ)*(2*divisorConstant δ*Z*P)+20*(B:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hwidth (by positivity : 0≤2*divisorConstant δ*Z*P)
    nlinarith only [hm,hwidth]
  have hm := mul_le_mul_of_nonneg_left hinner (by positivity : 0≤2*divisorConstant δ*X*P)
  have hPP : P≤P^2 := by nlinarith only [hP]
  have hsave := mul_le_mul_of_nonneg_left hPP
    (by positivity : 0≤40*divisorConstant δ*X*(B:ℝ))
  have he : (B:ℝ)*P^2=(B:ℝ)^(1+4*δ) := by
    have hexp : 4*δ=(2*δ)*2 := by ring
    rw [Real.rpow_add hbpos,Real.rpow_one,hexp,Real.rpow_mul_natCast hbpos.le]
  dsimp only [valueBudget]
  rw [scaled_square_rpow 4 (by norm_num),scaled_square_rpow _ (by positivity),←he]
  change (2*divisorConstant δ*(X*P))*
    ((4*(B:ℝ)+1)*(2*divisorConstant δ*(Z*P))+4*(4*(B:ℝ)+1))≤_
  dsimp [valueConstant]
  change _≤(20*(divisorConstant δ)^2*X*Z+40*divisorConstant δ*X)*((B:ℝ)*P^2)
  nlinarith only [hm,hsave]

end ActualGaussianExceptionalGrowth318
