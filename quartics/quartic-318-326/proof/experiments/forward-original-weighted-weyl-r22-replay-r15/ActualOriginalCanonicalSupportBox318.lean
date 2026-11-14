module
public import ActualOriginalMinorCorrelationIntegral318
public section
noncomputable section
namespace ActualOriginalCanonicalSupportBox318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalFiniteBoxProduct318

@[expose] def centeredBox (H : ℤ) : Finset (Coordinates ℤ) :=
  originalBox (Finset.Icc (-H) H) (Finset.Icc (-H) H) (Finset.Icc (-H) H)
    (Finset.Icc (-H) H) (Finset.Icc (-H) H)

lemma actual_integer_interval_of_real_abs (z H : ℤ) (hz : |(z : ℝ)|≤(H : ℝ)) :
    z∈Finset.Icc (-H) H := by
  apply Finset.mem_Icc.mpr
  have hh := abs_le.mp hz
  exact_mod_cast hh

lemma actual_original_norm_in_box (z : Coordinates ℤ) (H : ℤ)
    (hz : ‖integerEmbed z‖≤(H : ℝ)) : z∈centeredBox H := by
  simp only [integerEmbed,Prod.norm_def,max_le_iff,Real.norm_eq_abs] at hz
  exact Finset.mem_product.mpr ⟨
    Finset.mem_product.mpr ⟨actual_integer_interval_of_real_abs _ _ hz.1.1,
      actual_integer_interval_of_real_abs _ _ hz.1.2⟩,
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨actual_integer_interval_of_real_abs _ _ hz.2.1.1,
        actual_integer_interval_of_real_abs _ _ hz.2.1.2⟩,
      actual_integer_interval_of_real_abs _ _ hz.2.2⟩⟩

/-- Compactness produces a fixed original product-norm support radius,
chosen before any scale. No continuity or nonempty-support premise is needed. -/
theorem actual_compact_support_radius (W : Coordinates ℝ → ℝ)
    (hc : HasCompactSupport W) :
    ∃ R : ℝ, 1≤R ∧ ∀ x, W x≠0 → ‖x‖≤R := by
  obtain ⟨R,hR⟩ := hc.isCompact.bddAbove_image
    (continuous_norm.continuousOn : ContinuousOn (fun x : Coordinates ℝ => ‖x‖) (tsupport W))
  refine ⟨max 1 R,le_max_left _ _,fun x hx => ?_⟩
  exact (hR ⟨x,subset_tsupport W hx,rfl⟩).trans (le_max_right _ _)

/-- A literal integer box supports the actual scaled W. Its radius is
ceil(R*B), not an arbitrary scale-dependent finite support. -/
theorem actual_scaled_support_box (W : Coordinates ℝ → ℝ) (R B : ℝ)
    (hB : 0<B) (hR : ∀ x, W x≠0 → ‖x‖≤R) :
    ∀ z∉centeredBox ⌈R*B⌉, latticeWeight B W z=0 := by
  intro z hz
  by_contra hn
  apply hz
  apply actual_original_norm_in_box
  have hw : W (B⁻¹ • integerEmbed z)≠0 := by
    intro h
    apply hn
    simp only [latticeWeight,h,Complex.ofReal_zero]
  have hh := hR (B⁻¹ • integerEmbed z) hw
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hB] at hh
  have hd : ‖integerEmbed z‖/B≤R := by
    simpa only [div_eq_mul_inv,mul_comm] using hh
  exact ((div_le_iff₀ hB).mp hd).trans (Int.le_ceil (R*B))

/-- One produced radius works for every positive real scale. -/
theorem actual_compact_canonical_support (W : Coordinates ℝ → ℝ)
    (hc : HasCompactSupport W) :
    ∃ R : ℝ, 1≤R ∧ ∀ B : ℝ, 0<B →
      ∀ z∉centeredBox ⌈R*B⌉, latticeWeight B W z=0 := by
  obtain ⟨R,hR,hs⟩ := actual_compact_support_radius W hc
  exact ⟨R,hR,fun B hB => actual_scaled_support_box W R B hB hs⟩

end ActualOriginalCanonicalSupportBox318
