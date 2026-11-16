module
public import ActualOriginalAllPrimeFactors318
public section
noncomputable section
namespace ActualOriginalExceptionalProducts318
open ActualOriginalAllPrimeFactors318 ActualGoodPrimeDensityProduct318
set_option maxHeartbeats 24000000

@[expose] def exceptional318 (p : ℕ) : ℝ :=
  (if p=2 then 8/7 else 1)*(if p=3 then 16/13 else 1)*(if p=53 then 2916/2863 else 1)
@[expose] def exceptional326 (p : ℕ) : ℝ :=
  (if p=2 then 8/7 else 1)*(if p=163 then 26896/26733 else 1)

lemma actual_318_factorization (p : ℕ) : density318 p=factor 318 p*exceptional318 p := by
  classical
  by_cases h2 : p=2
  · subst p
    norm_num [density318,factor,Good,exceptional318]
  by_cases h3 : p=3
  · subst p
    norm_num [density318,factor,Good,exceptional318]
  by_cases h53 : p=53
  · subst p
    norm_num [density318,factor,Good,exceptional318]
  by_cases hp : p.Prime
  · have hg : Good 318 p := ⟨hp,h2,original_318_good_remaining p hp h2 h3 h53⟩
    simp only [density318,factor,exceptional318,if_pos hp,if_pos hg,if_neg h2,if_neg h3,if_neg h53,mul_one]
  · have hg : ¬Good 318 p := fun h => hp h.1
    simp only [density318,factor,exceptional318,if_neg hp,if_neg hg,if_neg h2,if_neg h3,if_neg h53,mul_one]
lemma actual_326_factorization (p : ℕ) : density326 p=factor 326 p*exceptional326 p := by
  classical
  by_cases h2 : p=2
  · subst p
    norm_num [density326,factor,Good,exceptional326]
  by_cases h163 : p=163
  · subst p
    norm_num [density326,factor,Good,exceptional326]
  by_cases hp : p.Prime
  · have hg : Good 326 p := ⟨hp,h2,original_326_good_remaining p hp h2 h163⟩
    simp only [density326,factor,exceptional326,if_pos hp,if_pos hg,if_neg h2,if_neg h163,mul_one]
  · have hg : ¬Good 326 p := fun h => hp h.1
    simp only [density326,factor,exceptional326,if_neg hp,if_neg hg,if_neg h2,if_neg h163,mul_one]

lemma exceptional318_pos (p : ℕ) : 0<exceptional318 p := by
  unfold exceptional318
  positivity
lemma exceptional326_pos (p : ℕ) : 0<exceptional326 p := by
  unfold exceptional326
  positivity

/-- Each finite exceptional product is built at its actual prime,
including the dyadic factor derived from the original involution. -/
lemma actual_exceptional318_product :
    HasProd exceptional318 ((8/7:ℝ)*(16/13)*(2916/2863)) := by
  have h2 : HasProd (fun p : ℕ => if p=2 then (8/7:ℝ) else 1) (8/7) := hasProd_ite_eq 2 _
  have h3 : HasProd (fun p : ℕ => if p=3 then (16/13:ℝ) else 1) (16/13) := hasProd_ite_eq 3 _
  have h53 : HasProd (fun p : ℕ => if p=53 then (2916/2863:ℝ) else 1) (2916/2863) := hasProd_ite_eq 53 _
  exact (h2.mul h3).mul h53
lemma actual_exceptional326_product : HasProd exceptional326 ((8/7:ℝ)*(26896/26733)) := by
  have h2 : HasProd (fun p : ℕ => if p=2 then (8/7:ℝ) else 1) (8/7) := hasProd_ite_eq 2 _
  have h163 : HasProd (fun p : ℕ => if p=163 then (26896/26733:ℝ) else 1) (26896/26733) := hasProd_ite_eq 163 _
  exact h2.mul h163

end ActualOriginalExceptionalProducts318
