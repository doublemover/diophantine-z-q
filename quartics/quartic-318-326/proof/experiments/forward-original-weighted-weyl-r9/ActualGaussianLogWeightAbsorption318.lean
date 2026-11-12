module
public import ActualGaussianExceptionalGrowth318
public section
noncomputable section
namespace ActualGaussianLogWeightAbsorption318
open scoped BigOperators
open OriginalBadSliceLogWeight318 ActualGaussianLogBudget318 ActualGaussianHeightGrowth318
set_option maxHeartbeats 12000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def exponent (ε : ℝ) : ℝ := ε/((Fintype.card J:ℝ)+1)
@[expose] def weightConstant (γ : J → ℤ) (η : ℝ) : ℝ :=
  ∏ j, (Real.log (2+|(γ j:ℝ)|)+2/η)
@[expose] def envelopeConstant (κ : ℤ) (η : ℝ) : ℝ :=
  Real.log (heightConstant κ)+74/η

lemma exponent_pos (ε : ℝ) (hε : 0<ε) : 0<exponent (J := J) ε := by
  dsimp [exponent]
  positivity
lemma exponent_total (ε : ℝ) :
    exponent (J := J) ε*((Fintype.card J:ℝ)+1)=ε := by
  dsimp [exponent]
  field_simp
lemma weightConstant_nonneg (γ : J → ℤ) (η : ℝ) (hη : 0<η) : 0≤weightConstant γ η := by
  apply Finset.prod_nonneg
  intro j _
  have hh := Real.log_nonneg (by positivity : (1:ℝ)≤2+|(γ j:ℝ)|)
  positivity
lemma envelopeConstant_nonneg (κ : ℤ) (η : ℝ) (hη : 0<η) : 0≤envelopeConstant κ η := by
  have hh := Real.log_nonneg (heightConstant_one κ)
  dsimp [envelopeConstant]
  positivity

/-- Each ORIGINAL logarithmic factor is bounded explicitly, using the
actual form coefficient. No eventual weight bound or free constant is assumed. -/
lemma original_log_factor (B : ℕ) (hB : 1≤B) (g : ℤ) (η : ℝ) (hη : 0<η) :
    Real.log (ceilingTerm B g)≤(Real.log (2+|(g:ℝ)|)+2/η)*(B:ℝ)^η := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hp : 1≤(B:ℝ)^η := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hb hη.le
  have hlog := Real.log_le_rpow_div hbpos.le hη
  have hc := Real.log_nonneg (by positivity : (1:ℝ)≤2+|(g:ℝ)|)
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hce : Real.log (ceilingTerm B g)=Real.log (2+|(g:ℝ)|)+2*Real.log (B:ℝ) := by
    dsimp [ceilingTerm]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hbpos.ne'),Real.log_pow]
    norm_num
  rw [hce]
  nlinarith only [hlog,hm]

lemma original_weight_growth (B : ℕ) (hB : 1≤B) (γ : J → ℤ) (η : ℝ) (hη : 0<η) :
    weightCeiling B γ≤weightConstant γ η*(B:ℝ)^(η*(Fintype.card J:ℝ)) := by
  have hh := Finset.prod_le_prod
    (fun j (_ : j∈Finset.univ) => Real.log_nonneg (ceilingTerm_one_le B hB (γ j)))
    (fun j _ => original_log_factor B hB (γ j) η hη)
  have hp : ((B:ℝ)^η)^(Fintype.card J)=(B:ℝ)^(η*(Fintype.card J:ℝ)) :=
    (Real.rpow_mul_natCast (by positivity) η (Fintype.card J)).symm
  simpa only [weightCeiling,weightConstant,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,hp] using hh

lemma envelope_growth (B : ℕ) (hB : 1≤B) (κ : ℤ) (η : ℝ) (hη : 0<η) :
    logEnvelope κ B≤envelopeConstant κ η*(B:ℝ)^η := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hp : 1≤(B:ℝ)^η := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hb hη.le
  have hc := Real.log_nonneg (heightConstant_one κ)
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hl := Real.log_le_rpow_div (zero_le_one.trans hb) hη
  dsimp [logEnvelope,envelopeConstant]
  nlinarith only [hm,hl]

/-- Original weight AND the extra true-quartic logarithmic envelope are
absorbed simultaneously by B^epsilon. The shared exponent is epsilon/(k+1),
so an arbitrary finite number of original prime-form factors is handled. -/
theorem actual_weight_height_absorption (B : ℕ) (hB : 1≤B) (κ : ℤ) (γ : J → ℤ)
    (ε : ℝ) (hε : 0<ε) :
    weightCeiling B γ≤weightConstant γ (exponent (J := J) ε)*(B:ℝ)^ε ∧
    weightCeiling B γ*logEnvelope κ B≤
      (weightConstant γ (exponent (J := J) ε)*envelopeConstant κ (exponent (J := J) ε))*
        (B:ℝ)^ε := by
  let η := exponent (J := J) ε
  have hη : 0<η := exponent_pos ε hε
  have htotal : η*((Fintype.card J:ℝ)+1)=ε := exponent_total ε
  have hk : η*(Fintype.card J:ℝ)≤ε := by nlinarith only [htotal,hη]
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  have hW := original_weight_growth B hB γ η hη
  have hE := envelope_growth B hB κ η hη
  have hC := weightConstant_nonneg γ η hη
  have hCE := envelopeConstant_nonneg κ η hη
  constructor
  · exact hW.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hk) hC)
  · have hm := mul_le_mul hW hE (logEnvelope_nonneg κ B hB) (by positivity)
    have he : (weightConstant γ η*(B:ℝ)^(η*(Fintype.card J:ℝ)))*
        (envelopeConstant κ η*(B:ℝ)^η)=
          (weightConstant γ η*envelopeConstant κ η)*(B:ℝ)^ε := by
      have hexp : η*(Fintype.card J:ℝ)+η=ε := by nlinarith only [htotal]
      rw [show (weightConstant γ η*(B:ℝ)^(η*(Fintype.card J:ℝ)))*
          (envelopeConstant κ η*(B:ℝ)^η)=
        (weightConstant γ η*envelopeConstant κ η)*
          ((B:ℝ)^(η*(Fintype.card J:ℝ))*(B:ℝ)^η) by ring,
        ←Real.rpow_add hbpos,hexp]
    exact hm.trans_eq he

end ActualGaussianLogWeightAbsorption318
