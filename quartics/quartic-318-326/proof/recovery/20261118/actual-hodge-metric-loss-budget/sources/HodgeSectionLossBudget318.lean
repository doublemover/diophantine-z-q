module
public import DirectHodgeSectionHeight318
public section
noncomputable section
namespace HodgeSectionLossBudget318
open NumberField Height SectionHeight318 FiveContactProducer318 ContactHeight318
open ContactMetricSections318 DirectHodgeSectionHeight318

/-- A numerical proof against the ORIGINAL strict cutoff 120. Bounding π by
4 and the integer product by 2^145 still permits an extra factor 2^28. -/
theorem slack :
    2*Real.log Real.pi+Real.log 210+Real.log sectionBound+Real.log 32+28*Real.log 2<120 := by
  have hn : (210:ℝ)*sectionBound*32*16 < 2^145 := by norm_num [sectionBound]
  have hsec : 0<sectionBound := by norm_num [sectionBound]
  have hl := Real.log_lt_log (by positivity : (0:ℝ)<210*sectionBound*32*16) hn
  rw [Real.log_pow] at hl
  rw [Real.log_mul (by positivity : (210:ℝ)*sectionBound*32≠0) (by norm_num : (16:ℝ)≠0),
    Real.log_mul (by positivity : (210:ℝ)*sectionBound≠0) (by norm_num : (32:ℝ)≠0),
    Real.log_mul (by norm_num : (210:ℝ)≠0) hsec.ne'] at hl
  have hp := Real.log_lt_log Real.pi_pos Real.pi_lt_four
  have h16 : Real.log (16:ℝ)=2*Real.log 4 := by
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow]
    norm_num
  rw [h16] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith [Real.log_two_lt_d9]

/-- Positive integer N clears actual finite-place defects of both sections;
E bounds an actual common archimedean loss. They are NOT asserted to exist.
Under N E ≤ 2^28 the original strict conclusion holds without enlarging 120.
The rational scale N does not change the projective ratio. -/
theorem height_with_loss {K : Type*} [Field K] [NumberField K]
    (H : FrameNorms K) (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (u v : ℤ) (a₀ a₁ : K) (ha₀ : a₀≠0)
    (hrel : a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀)
    (N : ℕ) (hN : 0<N) (E : ℝ) (hE : 0<E) (hNE : (N:ℝ)*E≤2^28)
    (ha : ∀ (w : InfinitePlace K) i, w (![a₀,a₁] i)*(H.arch w)^2≤sectionBound*E)
    (hf : ∀ (w : FinitePlace K) i, w (((210:K)*(N:K))*(![a₀,a₁] i))*(H.finiteNorm w)^2≤1) :
    pointHeight u v<2*(hYuan-Real.log Real.pi)+120 := by
  have hpos : (0:ℝ)<N := by exact_mod_cast hN
  have hnz : (N:K)≠0 := by exact_mod_cast hN.ne'
  have values (i : Fin 2) : ![(N:K)*a₀,(N:K)*a₁] i=(N:K)*(![a₀,a₁] i) := by
    fin_cases i <;> rfl
  have ha' (w : InfinitePlace K) (i : Fin 2) :
      w (![(N:K)*a₀,(N:K)*a₁] i)*(comparisonFrame H).arch w≤sectionBound*((N:ℝ)*E) := by
    rw [values,comparison_arch,map_mul]
    have hw : w (N:K)=(N:ℝ) := w.map_natCast N
    rw [hw]
    calc
      _ = (N:ℝ)*(w (![a₀,a₁] i)*(H.arch w)^2) := by ring
      _ ≤ (N:ℝ)*(sectionBound*E) := mul_le_mul_of_nonneg_left (ha w i) hpos.le
      _ = _ := by ring
  have hf' (w : FinitePlace K) (i : Fin 2) :
      w (![(N:K)*a₀,(N:K)*a₁] i)*(comparisonFrame H).finiteNorm w≤1 := by
    rw [values,comparison_finite,map_mul]
    have h := hf w i
    rw [map_mul,map_mul] at h
    calc
      _ = w (210:K)*w (N:K)*w (![a₀,a₁] i)*(H.finiteNorm w)^2 := by ring
      _ ≤ 1 := h
  have hr : (N:K)*a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*((N:K)*a₀) := by rw [hrel];ring
  have hs := rational_section_height ((N:K)*a₀) ((N:K)*a₁) (32*((u:ℚ)/(v:ℚ)))
    (mul_ne_zero hnz ha₀) hr (comparisonFrame H) (sectionBound*((N:ℝ)*E)) ha' hf'
  have hsec : (0:ℝ)<sectionBound := by norm_num [sectionBound]
  rw [comparison_degree,hdegree,Real.log_mul hsec.ne' (mul_pos hpos hE).ne'] at hs
  have hL := Real.log_le_log (mul_pos hpos hE) hNE
  rw [Real.log_pow] at hL
  norm_num only [Nat.cast_ofNat] at hL
  have hscale := rational_scale_loss ((u:ℚ)/(v:ℚ))
  rw [pointHeight_eq_contact_height,DetectorHeightTransfer318.rational_height_eq]
  linarith [slack]
end HodgeSectionLossBudget318
