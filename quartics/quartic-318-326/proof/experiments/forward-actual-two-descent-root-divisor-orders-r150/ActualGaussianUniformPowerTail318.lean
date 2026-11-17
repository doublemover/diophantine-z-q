module
public import ActualGaussianLogWeightAbsorption318
public section
noncomputable section
namespace ActualGaussianUniformPowerTail318
open ActualGaussianExceptionalGrowth318 ActualGaussianLogWeightAbsorption318
open ActualGaussianFullSourceTail318 ActualGaussianPowerSaving318 ActualGaussianLogBudget318
open ActualGaussianZeroStratum318 ActualOriginalLevelSource318
open OriginalBadSliceLogWeight318 OriginalGlobalBadMass318
set_option maxHeartbeats 18000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Reusable exact power comparison after an actual weight bound. -/
lemma weighted_power (B : ℕ) (hB : 1≤B) (w C c a e s : ℝ) (hC : 0≤C) (hc : 0≤c)
    (hw : w≤C*(B:ℝ)^e) (hes : a+e≤s) :
    w*c*(B:ℝ)^a≤C*c*(B:ℝ)^s := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hm := mul_le_mul_of_nonneg_right hw (mul_nonneg hc (Real.rpow_nonneg hbpos.le _))
  have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hes)
    (mul_nonneg hC hc)
  have he : C*(B:ℝ)^e*(c*(B:ℝ)^a)=C*c*(B:ℝ)^(a+e) := by
    rw [Real.rpow_add hbpos]
    ring
  calc
    _ ≤ C*(B:ℝ)^e*(c*(B:ℝ)^a) := by nlinarith only [hm]
    _ = C*c*(B:ℝ)^(a+e) := he
    _ ≤ _ := hp

@[expose] def mainConstant (κ : ℤ) (γ : J → ℤ) (ε : ℝ) : ℝ :=
  weightConstant γ (exponent (J := J) (ε/2))*
    (8*valueConstant κ (ε/8)+113246208*rankinCoefficient κ (ε/8))
@[expose] def errorConstant (κ : ℤ) (γ : J → ℤ) (ε : ℝ) : ℝ :=
  weightConstant γ (exponent (J := J) (ε/2))*
    (zeroConstant κ (ε/8)+25401600*rankinCoefficient κ (ε/8)+2*tailConstant (ε/8))+
  (weightConstant γ (exponent (J := J) (ε/2))*
    envelopeConstant κ (exponent (J := J) (ε/2)))*
      (25930800*rankinCoefficient κ (ε/8)/Real.log 3)

lemma constants_nonneg (κ : ℤ) (γ : J → ℤ) (ε : ℝ) (hε : 0<ε) :
    0≤mainConstant κ γ ε ∧ 0≤errorConstant κ γ ε := by
  have hd : 0<ε/8 := by linarith
  have he : 0<ε/2 := by linarith
  have hD := ActualDivisorSubpower318.divisorConstant_pos (ε/8) hd
  have hR := OriginalUniformEulerRankin318.rankinConstant_pos κ (ε/8) hd
  have hT := tailConstant_pos (ε/8)
  have hW := weightConstant_nonneg γ _ (exponent_pos (ε/2) he)
  have hE := envelopeConstant_nonneg κ _ (exponent_pos (ε/2) he)
  have hlog : 0<Real.log (3:ℝ) := Real.log_pos (by norm_num)
  dsimp [mainConstant,errorConstant,zeroConstant,valueConstant,rankinCoefficient]
  exact ⟨by positivity,by positivity⟩

/-- Quantitative full original weighted tail after ALL exponent renaming
and original logarithm absorption. The constants depend only on fixed
kappa, the finite original coefficient family and requested epsilon. -/
theorem actual_uniform_power_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 3≤Y) (γ : J → ℤ) (ε : ℝ) (hε : 0<ε) :
    ActualGaussianFullSourceTail318.mass B κ Y γ≤
      mainConstant κ γ ε*(B:ℝ)^(3+ε)/(Y:ℝ)+
        errorConstant κ γ ε*(B:ℝ)^((11:ℝ)/4+ε) := by
  let δ := ε/8
  let e := ε/2
  let C := weightConstant γ (exponent (J := J) e)
  let E := envelopeConstant κ (exponent (J := J) e)
  let W := weightCeiling B γ
  let A := rankinCoefficient κ δ
  have hd : 0<δ := by dsimp [δ];linarith
  have he : 0<e := by dsimp [e];linarith
  have hD := ActualDivisorSubpower318.divisorConstant_pos δ hd
  have hR := OriginalUniformEulerRankin318.rankinConstant_pos κ δ hd
  have hA : 0≤A := by dsimp [A,rankinCoefficient];positivity
  have hZ : 0≤zeroConstant κ δ := by dsimp [zeroConstant];positivity
  have hV : 0≤valueConstant κ δ := by dsimp [valueConstant];positivity
  have hTail := (tailConstant_pos δ).le
  have hC : 0≤C := weightConstant_nonneg γ _ (exponent_pos e he)
  have hE : 0≤E := envelopeConstant_nonneg κ _ (exponent_pos e he)
  have hW : 0≤W := weightCeiling_nonneg B hB γ
  have hEnv := logEnvelope_nonneg κ B hB
  obtain ⟨hw,hwe⟩ := actual_weight_height_absorption B hB κ γ e he
  change W≤C*(B:ℝ)^e at hw
  change W*logEnvelope κ B≤(C*E)*(B:ℝ)^e at hwe
  have hYpos : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hlog3 : 0<Real.log (3:ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<3)
    (show (3:ℝ)≤Y by exact_mod_cast hY)
  have hinv := one_div_le_one_div_of_le hlog3 hlog
  have hz := weighted_power B hB W C (zeroConstant κ δ) (2+2*δ) e ((11:ℝ)/4+ε)
    hC hZ hw (by dsimp [δ,e];linarith)
  have hv := weighted_power B hB W C (8*valueConstant κ δ) (3+4*δ) e (3+ε)
    hC (by positivity) hw (by dsimp [δ,e];linarith)
  have hmain := weighted_power B hB W C (113246208*A) (3+δ) e (3+ε)
    hC (by positivity) hw (by dsimp [δ,e];linarith)
  have hcy := weighted_power B hB W C (25401600*A+2*tailConstant δ) ((11:ℝ)/4+δ) e ((11:ℝ)/4+ε)
    hC (by positivity) hw (by dsimp [δ,e];linarith)
  have har := weighted_power B hB (W*logEnvelope κ B) (C*E) (25930800*A/Real.log 3)
    ((11:ℝ)/4+δ) e ((11:ℝ)/4+ε) (mul_nonneg hC hE) (by positivity) hwe
    (by dsimp [δ,e];linarith)
  have hi := mul_le_mul_of_nonneg_left hinv
    (by positivity : 0≤25930800*A*(W*logEnvelope κ B)*(B:ℝ)^((11:ℝ)/4+δ))
  have hvY := div_le_div_of_nonneg_right hv hYpos.le
  have hmY := div_le_div_of_nonneg_right hmain hYpos.le
  have hzero := mul_le_mul_of_nonneg_left (zero_growth B hB κ δ hd) hW
  have hvalue := mul_le_mul_of_nonneg_left (value_growth B hB κ δ hd)
    (by positivity : 0≤W*(8*(B:ℝ)^2/(Y:ℝ)))
  have hfull := actual_full_gaussian_tail B hB κ hκ Y hY γ δ hd
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hp : (B:ℝ)^2*(B:ℝ)^(1+4*δ)=(B:ℝ)^(3+4*δ) := by
    rw [show (3+4*δ:ℝ)=2+(1+4*δ) by ring,Real.rpow_add hb,Real.rpow_two]
  have hvY' : W*(8*(B:ℝ)^2/(Y:ℝ))*valueConstant κ δ*(B:ℝ)^(1+4*δ)≤
      C*(8*valueConstant κ δ)*(B:ℝ)^(3+ε)/(Y:ℝ) := by
    convert hvY using 1
    rw [←hp]
    ring
  change ActualGaussianFullSourceTail318.mass B κ Y γ≤_
  dsimp [ActualGaussianPowerSaving318.optimizedBudget] at hfull
  change ActualGaussianFullSourceTail318.mass B κ Y γ≤
    W*(zeroBudget B κ δ+(8*(B:ℝ)^2/(Y:ℝ))*valueBudget B κ δ+
      (A*113246208*(B:ℝ)^(3+δ)/(Y:ℝ)+
        (A*(25930800*logEnvelope κ B/Real.log (Y:ℝ)+25401600)+2*tailConstant δ)*
          (B:ℝ)^((11:ℝ)/4+δ))) at hfull
  change _≤(C*(8*valueConstant κ δ+113246208*A))*(B:ℝ)^(3+ε)/(Y:ℝ)+
    (C*(zeroConstant κ δ+25401600*A+2*tailConstant δ)+(C*E)*(25930800*A/Real.log 3))*
      (B:ℝ)^((11:ℝ)/4+ε)
  nlinarith only [hfull,hzero,hvalue,hz,hvY',hmY,hcy,har,hi]

end ActualGaussianUniformPowerTail318
