module
public import ActualOriginalMixedProductDifference318
public section
noncomputable section
namespace ActualOriginalUniformPairedMixedConstants318
open QuadricCRTAssembly318 ActualOriginalSmoothMixedDifference318
open ActualOriginalMixedProductDifference318
open scoped ContDiff

/-- Real form of the actual paired weight. Since W is real-valued, its
complex conjugate is unchanged when later cast into latticeWeight. -/
@[expose] def translatedPairedWeight (W : Coordinates ℝ → ℝ)
    (h x : Coordinates ℝ) : ℝ := W (x+h)*W x

lemma actual_first_difference (W : Coordinates ℝ → ℝ) (L : ℝ)
    (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖) (x u : Coordinates ℝ) :
    ‖W x-W (x+u)‖≤L*‖u‖ := by
  have hh := hl (x+u) x
  simpa only [norm_sub_rev,add_sub_cancel_left] using hh

lemma actual_paired_amplitude (W : Coordinates ℝ → ℝ) (A : ℝ) (hA : 0≤A)
    (ha : ∀ x, ‖W x‖≤A) (h x : Coordinates ℝ) :
    ‖translatedPairedWeight W h x‖≤A^2 := by
  unfold translatedPairedWeight
  rw [norm_mul,pow_two]
  exact mul_le_mul (ha _) (ha _) (norm_nonneg _) hA

lemma actual_paired_first_difference (W : Coordinates ℝ → ℝ) (A L : ℝ)
    (hA : 0≤A) (ha : ∀ x, ‖W x‖≤A)
    (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖) (h x u : Coordinates ℝ) :
    ‖translatedPairedWeight W h x-translatedPairedWeight W h (x+u)‖≤2*A*L*‖u‖ := by
  have h0 := actual_first_difference W L hl x u
  have h1 : ‖W (x+h)-W (x+u+h)‖≤L*‖u‖ := by
    simpa only [add_assoc,add_left_comm,add_comm] using actual_first_difference W L hl (x+h) u
  have he : translatedPairedWeight W h x-translatedPairedWeight W h (x+u)=
      W (x+h)*(W x-W (x+u))+(W (x+h)-W (x+u+h))*W (x+u) := by
    unfold translatedPairedWeight
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hb0 := mul_le_mul (ha (x+h)) h0 (norm_nonneg _) hA
  have hb1 := mul_le_mul h1 (ha (x+u)) (norm_nonneg _) ((norm_nonneg _).trans h1)
  nlinarith

lemma actual_paired_mixed_difference (W : Coordinates ℝ → ℝ) (A L D : ℝ)
    (ha : ∀ x, ‖W x‖≤A)
    (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖)
    (hd : ∀ x u v, ‖(W x-W (x+u))-(W (x+v)-W (x+v+u))‖≤D*‖u‖*‖v‖)
    (h x u v : Coordinates ℝ) :
    ‖(translatedPairedWeight W h x-translatedPairedWeight W h (x+u))-
      (translatedPairedWeight W h (x+v)-translatedPairedWeight W h (x+v+u))‖≤
      (2*A*D+2*L^2)*‖u‖*‖v‖ := by
  have hu₀ : ‖W (x+v+h)-W (x+v+u+h)‖≤L*‖u‖ := by
    simpa only [add_assoc,add_left_comm,add_comm] using actual_first_difference W L hl (x+v+h) u
  have hu₁ : ‖W (x+u+h)-W (x+v+u+h)‖≤L*‖v‖ := by
    simpa only [add_assoc,add_left_comm,add_comm] using actual_first_difference W L hl (x+u+h) v
  have hdu : ‖(W (x+h)-W (x+u+h))-(W (x+v+h)-W (x+v+u+h))‖≤D*‖u‖*‖v‖ := by
    simpa only [add_assoc,add_left_comm,add_comm] using hd (x+h) u v
  have hb := actual_mixed_product_bound
    (W (x+h)) (W (x+u+h)) (W (x+v+h)) (W (x+v+u+h))
    (W x) (W (x+u)) (W (x+v)) (W (x+v+u))
    A A (L*‖u‖) (L*‖v‖) (L*‖u‖) (L*‖v‖) (D*‖u‖*‖v‖) (D*‖u‖*‖v‖)
    (ha _) (ha _) hu₀ hu₁ (actual_first_difference W L hl x u)
    (actual_first_difference W L hl x v) hdu (hd x u v)
  change ‖(translatedPairedWeight W h x-translatedPairedWeight W h (x+u))-
    (translatedPairedWeight W h (x+v)-translatedPairedWeight W h (x+v+u))‖≤_ at hb
  convert hb using 1 <;> ring

/-- All amplitude/first/mixed constants are PRODUCED from the actual
smooth compact W before the translation h. No slice-dependent Hessian or
mixed-increment premise is supplied in this theorem. -/
theorem actual_smooth_uniform_paired_mixed_constants (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧ ∀ h x : Coordinates ℝ,
      ‖translatedPairedWeight W h x‖≤A^2 ∧
      (∀ u, ‖translatedPairedWeight W h x-translatedPairedWeight W h (x+u)‖≤2*A*L*‖u‖) ∧
      (∀ u v, ‖(translatedPairedWeight W h x-translatedPairedWeight W h (x+u))-
        (translatedPairedWeight W h (x+v)-translatedPairedWeight W h (x+v+u))‖≤
          (2*A*D+2*L^2)*‖u‖*‖v‖) := by
  obtain ⟨A,L,D,hA,hL,hD,ha,hl,hd⟩ := actual_smooth_mixed_constants W hW hc
  exact ⟨A,L,D,hA,hL,hD,fun h x => ⟨actual_paired_amplitude W A hA ha h x,
    fun u => actual_paired_first_difference W A L hA ha hl h x u,
    fun u v => actual_paired_mixed_difference W A L D ha hl hd h x u v⟩⟩

end ActualOriginalUniformPairedMixedConstants318
