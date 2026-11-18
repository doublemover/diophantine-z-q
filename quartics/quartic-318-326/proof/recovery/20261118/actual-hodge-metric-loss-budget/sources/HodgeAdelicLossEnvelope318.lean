module
public import HodgeSectionLossBudget318
public section
noncomputable section
namespace HodgeAdelicLossEnvelope318
open NumberField Height SectionHeight318 FiveContactProducer318 ContactHeight318
open ContactMetricSections318 DirectHodgeSectionHeight318
variable {K : Type*} [Field K] [NumberField K]

/-- Divide a comparison norm by a positive finite-support loss at each place.
No principal-ideal assumption on these scalar losses is made. -/
@[expose] def discounted (F L : FrameNorms K) : FrameNorms K where
  arch w := F.arch w/L.arch w
  finiteNorm w := F.finiteNorm w/L.finiteNorm w
  arch_pos w := div_pos (F.arch_pos w) (L.arch_pos w)
  finite_pos w := div_pos (F.finite_pos w) (L.finite_pos w)
  finite_support := F.finite_support.div L.finite_support

theorem logSum_discounted (F L : FrameNorms K) :
    (discounted F L).logSum=F.logSum-L.logSum := by
  classical
  unfold FrameNorms.logSum discounted
  dsimp only
  simp_rw [Real.log_div (F.arch_pos _).ne' (L.arch_pos _).ne',mul_sub,
    Real.log_div (F.finite_pos _).ne' (L.finite_pos _).ne']
  rw [Finset.sum_sub_distrib,finsum_sub_distrib (log_finite_support F.finite_support)
    (log_finite_support L.finite_support)]
  ring

/-- Positive log loss averaged using the number field's existing multiplicities
and finite-place normalization. -/
@[expose] def loss (L : FrameNorms K) : ℝ := L.logSum/(Module.finrank ℚ K:ℝ)

theorem discounted_degree (F L : FrameNorms K) :
    (discounted F L).normalizedDegree=F.normalizedDegree+loss L := by
  rw [FrameNorms.normalizedDegree,logSum_discounted,FrameNorms.normalizedDegree,loss]
  ring

private theorem maxOne_support {ι : Type*} (f : ι → ℝ) (hf : Function.HasFiniteMulSupport f) :
    Function.HasFiniteMulSupport (fun i => max 1 (f i)) := by
  apply hf.subset
  intro i hi
  simp only [Function.mem_mulSupport] at hi ⊢
  intro he
  exact hi (by simp [he])

variable {ι : Type*} [Finite ι]
/-- The ACTUAL positive excesses: retain only local quotients above one.
At infinity divide by the proven section bound budget C. -/
@[expose] def envelope (F : FrameNorms K) (a : ι → K) (ha : a≠0) (C : ℝ) : FrameNorms K where
  arch w := max 1 (localMax w.val a * F.arch w / C)
  finiteNorm w := max 1 (localMax w.val a * F.finiteNorm w)
  arch_pos w := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  finite_pos w := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  finite_support := maxOne_support _ ((finite_localMax_support ha).mul F.finite_support)

theorem envelope_arch (F : FrameNorms K) (a : ι → K) (ha : a≠0) (C : ℝ) (hC : 0<C)
    (w : InfinitePlace K) (i : ι) :
    w (a i)*(discounted F (envelope F a ha C)).arch w≤C := by
  change w (a i)*(F.arch w/(envelope F a ha C).arch w)≤C
  rw [←mul_div_assoc,div_le_iff₀ ((envelope F a ha C).arch_pos w)]
  have hi : w (a i) ≤ localMax w.val a := Finite.le_ciSup_of_le i le_rfl
  apply le_trans (mul_le_mul_of_nonneg_right hi (F.arch_pos w).le)
  change localMax w.val a*F.arch w ≤ C*max 1 (localMax w.val a*F.arch w/C)
  rw [mul_comm C,←div_le_iff₀ hC]
  exact le_max_right _ _

theorem envelope_finite (F : FrameNorms K) (a : ι → K) (ha : a≠0) (C : ℝ)
    (w : FinitePlace K) (i : ι) :
    w (a i)*(discounted F (envelope F a ha C)).finiteNorm w≤1 := by
  change w (a i)*(F.finiteNorm w/(envelope F a ha C).finiteNorm w)≤1
  rw [←mul_div_assoc,div_le_iff₀ ((envelope F a ha C).finite_pos w),one_mul]
  have hi : w (a i) ≤ localMax w.val a := Finite.le_ciSup_of_le i le_rfl
  apply le_trans (mul_le_mul_of_nonneg_right hi (F.finite_pos w).le)
  exact le_max_right _ _

theorem pair_ne_zero (a₀ a₁ : K) (h₀ : a₀≠0) : (![a₀,a₁] : Fin 2 → K)≠0 := by
  intro h
  exact h₀ (by simpa using congrFun h 0)

/-- Single remaining quantitative condition on the original two coordinates
and PRE-SPECIFIED Hodge norm. Positive defects at different places aggregate
with their actual weights. No choice of clearing integer, metric chosen from
the coordinates, or source-point classification is a premise. -/
theorem height_from_actual_loss (H : FrameNorms K) (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (u v : ℤ) (a₀ a₁ : K) (h₀ : a₀≠0)
    (hrel : a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀)
    (hLoss : loss (envelope (comparisonFrame H) ![a₀,a₁] (pair_ne_zero a₀ a₁ h₀) sectionBound)
      ≤28*Real.log 2) :
    pointHeight u v<2*(hYuan-Real.log Real.pi)+120 := by
  have hsec : 0<sectionBound := by norm_num [sectionBound]
  let F := comparisonFrame H
  let a : Fin 2 → K := ![a₀,a₁]
  have hA : a≠0 := pair_ne_zero a₀ a₁ h₀
  let L := envelope F a hA sectionBound
  have hs := rational_section_height a₀ a₁ (32*((u:ℚ)/(v:ℚ))) h₀ hrel
    (discounted F L) sectionBound (envelope_arch F a hA sectionBound hsec) (envelope_finite F a hA sectionBound)
  rw [discounted_degree] at hs
  change Height.logHeight₁ (32*((u:ℚ)/(v:ℚ))) ≤ (comparisonFrame H).normalizedDegree+loss L+Real.log sectionBound at hs
  rw [comparison_degree,hdegree] at hs
  have hL : loss L≤28*Real.log 2 := hLoss
  have hscale := rational_scale_loss ((u:ℚ)/(v:ℚ))
  rw [pointHeight_eq_contact_height,DetectorHeightTransfer318.rational_height_eq]
  linarith [HodgeSectionLossBudget318.slack]
end HodgeAdelicLossEnvelope318
