module
public import ActualSamePositionBoxTail318
public section
noncomputable section
namespace ActualSamePositionWeightedTail318
open scoped BigOperators
open ActualSamePositionDivisors318 ActualSamePositionBoxTail318 ActualDivisorSubpower318
open OriginalBadSliceLogWeight318 ActualGaussianLogWeightAbsorption318 ActualGaussianGrowingCutoff318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def tripleWeight (γ : J → ℤ) {B : ℕ} (v : Triple B) : ℝ :=
  ∏ j,Real.log (max 1 (((v.1.1^2+v.2.1.1^2+γ j*v.2.2.1^2).natAbs:ℝ)))
lemma tripleWeight_nonneg (γ : J → ℤ) {B : ℕ} (v : Triple B) : 0≤tripleWeight γ v :=
  Finset.prod_nonneg (fun _ _ => Real.log_nonneg (le_max_left _ _))
lemma tripleWeight_bound (B : ℕ) (hB : 1≤B) (γ : J → ℤ) (v : Triple B) :
    tripleWeight γ v≤weightCeiling B γ := by
  apply Finset.prod_le_prod
  · intro j _
    exact Real.log_nonneg (le_max_left _ _)
  · intro j _
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    apply max_le (ceilingTerm_one_le B hB (γ j))
    have hz := form_abs_bound B (γ j) v.1.1 v.2.1.1 v.2.2.1
      (Finset.mem_Icc.mp v.1.2) (Finset.mem_Icc.mp v.2.1.2) (Finset.mem_Icc.mp v.2.2.2)
    have hn : ((v.1.1^2+v.2.1.1^2+γ j*v.2.2.1^2).natAbs:ℤ)≤
        (2+|γ j|)*(B:ℤ)^2 := by simpa only [Int.natCast_natAbs] using hz
    dsimp [ceilingTerm]
    exact_mod_cast hn
@[expose] def mass (B Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  exact ∑ v : Source B Y,tripleWeight γ v.1
lemma actual_mass_bound (B : ℕ) (hB : 1≤B) (Y : ℕ) (hY : 2≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    mass B Y γ≤weightCeiling B γ*countBudget B Y δ := by
  classical
  have hc := actual_same_position_count B Y hY δ hδ
  have hw : mass B Y γ≤(Nat.card (Source B Y):ℝ)*weightCeiling B γ := by
    calc
      _ ≤ ∑ _v : Source B Y,weightCeiling B γ :=
        Finset.sum_le_sum (fun v _ => tripleWeight_bound B hB γ v.1)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  exact hw.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hc (weightCeiling_nonneg B hB γ))

lemma actual_count_growth (B : ℕ) (hB : 1≤B) (Y : ℕ) (δ : ℝ) (hδ : 0<δ) :
    countBudget B Y δ≤9*(B:ℝ)^2+
      (18*divisorConstant δ*(2:ℝ)^δ)*(B:ℝ)^(3+2*δ)/(Y:ℝ) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hD := (divisorConstant_pos δ hδ).le
  have hb2 : (1:ℝ)≤(B:ℝ)^2 := one_le_pow₀ hb
  have hn := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(B:ℝ)^2+1)
    (by nlinarith only [hb2] : (B:ℝ)^2+1≤2*(B:ℝ)^2) hδ.le
  rw [ActualGaussianExceptionalGrowth318.scaled_square_rpow 2 (by norm_num)] at hn
  have hwidth : (2*(B:ℝ)+1)^2≤9*(B:ℝ)^2 := by nlinarith
  have hi := mul_le_mul_of_nonneg_left hn
    (by positivity : 0≤(2*(B:ℝ)/(Y:ℝ))*divisorConstant δ)
  have hm := mul_le_mul hwidth (add_le_add_left hi 1) (by positivity) (by positivity)
  have hp : (B:ℝ)^3*(B:ℝ)^(2*δ)=(B:ℝ)^(3+2*δ) := by
    rw [Real.rpow_add hbpos,Real.rpow_natCast]
  dsimp [countBudget]
  calc
    _ ≤ 9*(B:ℝ)^2*(1+(2*(B:ℝ)/(Y:ℝ))*divisorConstant δ*((2:ℝ)^δ*(B:ℝ)^(2*δ))) := hm
    _ = _ := by rw [←hp];ring

@[expose] def sameConstant (γ : J → ℤ) : ℝ :=
  (9+18*divisorConstant ((1:ℝ)/1000)*(2:ℝ)^((1:ℝ)/1000))*
    weightConstant γ (exponent (J := J) ((1:ℝ)/1000))

/-- A complete same-position large-prime power saving, with the actual
zero-a stratum and finite divisor producer. No generic box-sieve theorem
or prime-distribution bound is assumed. -/
theorem actual_same_position_growing_tail (B : ℕ) (hB : 1≤B) (Y : ℕ)
    (hY : cutoff 0 B≤Y) (γ : J → ℤ) :
    mass B Y γ≤sameConstant γ*(B:ℝ)^(3-(1:ℝ)/200) := by
  let δ : ℝ := (1:ℝ)/1000
  let C := weightConstant γ (exponent (J := J) δ)
  let W := weightCeiling B γ
  let D := 18*divisorConstant δ*(2:ℝ)^δ
  have hd : 0<δ := by norm_num [δ]
  have hC : 0≤C := weightConstant_nonneg γ _ (exponent_pos δ hd)
  have hD : 0≤D := by have hh := divisorConstant_pos δ hd;dsimp [D];positivity
  have hW : 0≤W := weightCeiling_nonneg B hB γ
  have hw : W≤C*(B:ℝ)^δ := (actual_weight_height_absorption B hB 0 γ δ hd).1
  have hY2 : 2≤Y := by have hh := (cutoff_three 0 B).trans hY;omega
  have hm := actual_mass_bound B hB Y hY2 γ δ hd
  have hc := mul_le_mul_of_nonneg_left (actual_count_growth B hB Y δ hd) hW
  have hfirst := ActualGaussianUniformPowerTail318.weighted_power B hB W C 9 2 δ
    (3-(1:ℝ)/200) hC (by norm_num) hw (by norm_num [δ])
  norm_num only [Real.rpow_two] at hfirst
  have hsecond := ActualGaussianUniformPowerTail318.weighted_power B hB W C D (3+2*δ) δ
    (3+3*δ) hC hD hw (by ring_nf)
  have hYpos : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hsecY := div_le_div_of_nonneg_right hsecond hYpos.le
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hcut : (B:ℝ)^((1:ℝ)/100)≤(Y:ℝ) :=
    (cutoff_power 0 B).trans (by exact_mod_cast hY)
  have hdiv := div_le_div_of_nonneg_left
    (by positivity : 0≤C*D*(B:ℝ)^(3+3*δ))
    (Real.rpow_pos_of_pos hbpos ((1:ℝ)/100)) hcut
  have hpow := Real.rpow_le_rpow_of_exponent_le hb
    (by norm_num [δ] : 3+3*δ-(1:ℝ)/100≤3-(1:ℝ)/200)
  have hpow' := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hD)
  have hdiv' : C*D*(B:ℝ)^(3+3*δ)/(Y:ℝ)≤C*D*(B:ℝ)^(3-(1:ℝ)/200) := by
    calc
      _ ≤ C*D*(B:ℝ)^(3+3*δ)/(B:ℝ)^((1:ℝ)/100) := hdiv
      _ = C*D*(B:ℝ)^(3+3*δ-(1:ℝ)/100) := by rw [Real.rpow_sub hbpos];ring
      _ ≤ _ := hpow'
  change _≤(9+D)*C*(B:ℝ)^(3-(1:ℝ)/200)
  change mass B Y γ≤W*countBudget B Y δ at hm
  change W*countBudget B Y δ≤W*(9*(B:ℝ)^2+D*(B:ℝ)^(3+2*δ)/(Y:ℝ)) at hc
  nlinarith only [hm,hc,hfirst,hsecY,hdiv']

end ActualSamePositionWeightedTail318
