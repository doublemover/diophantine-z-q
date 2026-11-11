module
public import ScalarForwardWitness318
public section
noncomputable section
namespace ScalarPoleRealDomain318
open CircuitReplay ScalarForwardWitness318
set_option maxHeartbeats 0

/-- A deliberately loose quantitative bound suffices for the actual scalar
pole range. The stored half-trace and norm are the original source entries. -/
theorem packed_bound (w : Assignment) (n : ℤ)
    (hr : 10<inputR (w 0)) (hf0 : 0≤w 33) (hf1 : w 33≤1)
    (hH0 : (1/100:ℚ)< |w 37|) (hH1 : |w 37|≤1)
    (hR : |ActualScalarRoot318.inverseNorm n|<1) :
    0<W w n ∧ W w n<10 := by
  let r := inputR (w 0)
  have hr0 : 0<r := by dsimp [r]; linarith
  have hH : w 37≠0 := abs_pos.mp (by linarith)
  have hN2 : (w 37)^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hH1
  have hr2 : 1<r^2 := by nlinarith
  have hx : (w 37/r)^2<1 := by
    rw [div_pow]
    exact (div_lt_one (sq_pos_of_pos hr0)).mpr (by linarith)
  have hy : 2*w 33/r<1 := (div_lt_one hr0).mpr (by dsimp [r]; linarith)
  have hy0 : 0≤2*w 33/r := div_nonneg (by positivity) (le_of_lt hr0)
  have hN0 : 1≤N w := by change 1≤1+(w 37/r)^2+2*w 33/r; nlinarith [sq_nonneg (w 37/r)]
  have hN3 : N w<3 := by change 1+(w 37/r)^2+2*w 33/r<3; linarith
  have hH2 : (1/10000:ℚ)<(w 37)^2 := by
    nlinarith [sq_abs (w 37),sq_nonneg (|w 37|-1/100)]
  have hr29 : (10000:ℚ)<r^29 := by
    calc
      (10000:ℚ)<10^29 := by norm_num
      _ ≤r^29 := pow_le_pow_left₀ (by norm_num) (le_of_lt hr) _
  have hden : 1<(w 37)^2*r^29 := by
    calc
      (1:ℚ)=(1/10000)*10000 := by norm_num
      _ < (w 37)^2*r^29 := mul_lt_mul hH2 (le_of_lt hr29) (by norm_num) (sq_nonneg _)
  have hR2 : (ActualScalarRoot318.inverseNorm n)^2<1 := (sq_lt_one_iff_abs_lt_one _).mpr hR
  have hQ : r*(Q w n)^2<1 := by
    have he : r*(Q w n)^2=(ActualScalarRoot318.inverseNorm n)^2/((w 37)^2*r^29) := by
      dsimp [Q,r]
      field_simp [hH,ne_of_gt hr0] <;> ring
    rw [he]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hQ0 : 0≤r*(Q w n)^2 := mul_nonneg (le_of_lt hr0) (sq_nonneg _)
  change 0<(N w)^2+r*(Q w n)^2 ∧ (N w)^2+r*(Q w n)^2<10
  constructor <;> nlinarith [sq_nonneg (N w)]

/-- Actual scalar b is positive and below17 before any scalar point-pair
realization is invoked. No source-pole equation is assumed. -/
theorem pole_domain (w : Assignment) (n : ℤ)
    (hr : 10<inputR (w 0)) (hf0 : 0≤w 33) (hf1 : w 33≤1)
    (hH0 : (1/100:ℚ)< |w 37|) (hH1 : |w 37|≤1)
    (hR : |ActualScalarRoot318.inverseNorm n|<1) :
    0<poleInput w n ∧ poleInput w n<17 := by
  obtain ⟨hW0,hW10⟩ := packed_bound w n hr hf0 hf1 hH0 hH1 hR
  have ha : 10<114444*inputR (w 0) := by linarith
  have ha0 : 0<114444*inputR (w 0) := by linarith
  have hd : 0<1+114444*inputR (w 0) := by linarith
  have hq : 0<quotient w n := div_pos hW0 hd
  constructor
  · exact mul_pos ha0 (sq_pos_of_pos hq)
  · unfold poleInput quotient
    rw [div_pow,mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hd)).mpr
    have hw2 : (W w n)^2<100 := by nlinarith
    have hp := mul_lt_mul_of_pos_left hw2 ha0
    nlinarith [mul_pos ha0 (show 0<114444*inputR (w 0)-10 by linarith)]

end ScalarPoleRealDomain318
