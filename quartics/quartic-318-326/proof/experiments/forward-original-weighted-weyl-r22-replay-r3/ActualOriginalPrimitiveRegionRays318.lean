module
public import ActualOriginalPrimitiveRayFactor318
public section
noncomputable section
namespace ActualOriginalPrimitiveRegionRays318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalRealGoodRegion318
open ActualOriginalPositiveRayScaling318 ActualOriginalPrimitiveRayFactor318
open ActualPrimePointPrimitivity318 ActualOriginalCompactCircleCount318

@[expose] def goodPrimitivePoints {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ) : Set (Quadric κ) :=
  {u | Primitive κ u ∧ integerEmbed u.1∈region γ}

/-- The same ray factor preserves every positive original form and all
three positive coordinates in the good region. -/
theorem actual_good_primitive_factor {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (v : Quadric κ) (hv : integerEmbed v.1∈region γ) :
    ∃ d : ℕ, 0<d ∧ ∃ u : Quadric κ, u∈goodPrimitivePoints κ γ ∧
      v.1=scaleCoordinates (d : ℤ) u.1 := by
  have hva : (0 : ℝ)<(v.1.1.1 : ℝ) := hv.1
  obtain ⟨d,hd,u,hu,hua,he⟩ := actual_primitive_ray_factor κ v (by exact_mod_cast hva)
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd
  have hureg : integerEmbed u.1∈region γ := by
    apply (actual_region_scale_iff γ (d : ℝ) hdr (integerEmbed u.1)).mp
    rw [←actual_integer_scale_embed,←he]
    exact hv
  exact ⟨d,hd,u,⟨hu,hureg⟩,he⟩

lemma actual_weight_nonzero_region {J : Type*} [Fintype J] (γ : J → ℝ)
    (W : Coordinates ℝ → ℝ) (hW : ∀ y∈tsupport W,y∈region γ)
    (B : ℝ) (hB : 0<B) (v : Coordinates ℤ) (hv : latticeWeight B W v≠0) :
    integerEmbed v∈region γ := by
  have hw : W (B⁻¹ • integerEmbed v)≠0 := by
    intro hz
    apply hv
    simp only [latticeWeight,hz,Complex.ofReal_zero]
  have hh := hW _ (subset_tsupport W hw)
  apply (actual_region_scale_iff γ B⁻¹ (inv_pos.mpr hB) (integerEmbed v)).mp
  simpa only [actual_real_scale_smul] using hh

end ActualOriginalPrimitiveRegionRays318
