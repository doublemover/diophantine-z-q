module
public import FixedDetectorScales318
public import Mathlib.Order.Filter.AtTopBot.Field
public section
noncomputable section
namespace ScaledContactWeights318
open CircuitReplay Raw318FinalReplay ContactWeightWitness318 Filter
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def parameter (c t : ℚ) : ℚ := c^2*t
@[expose] def scaledWeight (c t : ℚ) : ℚ := c^10*weight (parameter c t)
@[expose] def delta (c t : ℚ) : ℚ := parameter c t-1

/-- Both later detector blocks use the same original free contact parameter
and a fixed root-derived square scale. All weights are evaluated, not supplied. -/
@[expose] def fill (offset : ℕ) (w : Assignment) (c t : ℚ) : Assignment := fun i =>
  if i=194+51*offset then parameter c t else
  if i=195+51*offset then (parameter c t)^2 else
  if i=196+51*offset then (parameter c t)^3 else
  if i=197+51*offset then (parameter c t)^3+(3081901/1205412)*(parameter c t)^4+(976393/602706)*(parameter c t)^5 else
  if i=198+51*offset then -c^2*delta c t else
  if i=199+51*offset then c^4*(delta c t)^2 else
  if i=200+51*offset then c^8*(delta c t)^4 else
  if i=201+51*offset then scaledWeight c t*(delta c t)^3 else
  if i=202+51*offset then (parameter c t)^2-(parameter c t)^3/2 else
  if i=203+51*offset then scaledWeight c t else
  if i=204+51*offset then parameter c t*scaledWeight c t*(delta c t)^3 else
  if i=205+51*offset then (scaledWeight c t)^2*(delta c t)^6 else
  if i=206+51*offset then (scaledWeight c t)^4*(delta c t)^11 else
  if i=207+51*offset then (scaledWeight c t)^7*(delta c t)^18 else
  if i=208+51*offset then (scaledWeight c t)^13*(delta c t)^36 else
  if i=209+51*offset then (scaledWeight c t)^25*(delta c t)^72 else
  w i

/-- The exact16 source weight rows of detector1. -/
theorem rows1 (S : ℚ) (w : Assignment) (c t : ℚ)
    (ht : t≠0) (hscale : c=w 143+w 145) (hinv : w 146=1/t)
    (hF : contact (parameter c t)≠0) :
    Constraints [r157 S,r158 S,r159 S,r160 S,r161 S,r162 S,r163 S,r164 S,r165 S,r166 S,r167 S,r168 S,r169 S,r170 S,r171 S,r172 S] (fill 0 w c t) := by
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · norm_num [r157,fill]
    all_goals
      rw [hinv,hscale]
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r158,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r159,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r160,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r161,fill]
    all_goals
      rw [hinv]
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r162,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r163,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r164,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r165,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r166,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r167,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r168,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r169,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r170,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r171,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r172,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
/-- The exact16 source weight rows of detector2. -/
theorem rows2 (S : ℚ) (w : Assignment) (c t : ℚ)
    (ht : t≠0) (hscale : c=w 145) (hinv : w 146=1/t)
    (hF : contact (parameter c t)≠0) :
    Constraints [r210 S,r211 S,r212 S,r213 S,r214 S,r215 S,r216 S,r217 S,r218 S,r219 S,r220 S,r221 S,r222 S,r223 S,r224 S,r225 S] (fill 1 w c t) := by
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · norm_num [r210,fill]
    all_goals
      rw [hinv,hscale]
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r211,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r212,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r213,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r214,fill]
    all_goals
      rw [hinv]
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r215,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r216,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r217,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r218,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r219,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r220,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r221,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r222,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r223,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r224,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
  · norm_num [r225,fill]
    all_goals
      dsimp [scaledWeight,weight,delta,parameter,contact] at hF ⊢
      field_simp [ht,hF] <;> ring
lemma parameter_limit (c : ℚ) (hc : c≠0) : Tendsto (parameter c) atTop atTop :=
  (tendsto_const_mul_atTop_of_pos (sq_pos_of_ne_zero hc)).mpr tendsto_id

lemma weight_limit (c : ℚ) (hc : c≠0) : Tendsto (scaledWeight c) atTop (𝓝 0) := by
  simpa [scaledWeight] using
    (ContactWeightLimits318.weight_limit.comp (parameter_limit c hc)).const_mul (c^10)

lemma weight7_limit (c : ℚ) (hc : c≠0) :
    Tendsto (fun t => (scaledWeight c t)^7*(delta c t)^18) atTop (𝓝 0) := by
  have ht := (ContactWeightLimits318.weight7_limit.comp (parameter_limit c hc)).const_mul (c^70)
  have he : (fun t => (scaledWeight c t)^7*(delta c t)^18)=
      fun t => c^70*((weight (parameter c t))^7*(parameter c t-1)^18) := by
    funext t
    dsimp [scaledWeight,delta]
    ring
  rw [he]
  simpa only [Function.comp_def,mul_zero] using ht

lemma weight25_limit (c : ℚ) (hc : c≠0) :
    Tendsto (fun t => (scaledWeight c t)^25*(delta c t)^72) atTop (𝓝 0) := by
  have ht := (ContactWeightLimits318.weight25_limit.comp (parameter_limit c hc)).const_mul (c^250)
  have he : (fun t => (scaledWeight c t)^25*(delta c t)^72)=
      fun t => c^250*((weight (parameter c t))^25*(parameter c t-1)^72) := by
    funext t
    dsimp [scaledWeight,delta]
    ring
  rw [he]
  simpa only [Function.comp_def,mul_zero] using ht

end ScaledContactWeights318
