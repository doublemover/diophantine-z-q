module
public import GlobalGeneratorPoints318
public import Mathlib.NumberTheory.Height.NumberField
public section
namespace GlobalSaturationHeight318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The actual absolute logarithmic x-height; the identity has xRep 0=1. -/
@[expose] def xHeight (Q:E.Point) : ℝ := NumberField.absLogHeight₁ (Q.xRep 0)

/-- This is the precise, still unproved global canonical-height interface.
It is not asserted to follow from the literal source. Its numerical bounds
are those obtained from the manuscript's duplication ideal estimates. -/
structure CanonicalData (H:E.Point→ℝ) : Prop where
  zero : H 0=0
  nonneg : ∀Q,0≤H Q
  zsmul : ∀(n:ℤ)(Q:E.Point),H (n • Q)=(n:ℝ)^2*H Q
  torsion : ∀(Q U:E.Point),U+U=0 → H (Q+U)=H Q
  lower : ∀Q,xHeight Q≤2*H Q+Real.log 392/3
  upper : ∀Q,2*H Q≤xHeight Q+Real.log 676/3
  heightP : xHeight P=Real.log 41

theorem canonical_neg {H:E.Point→ℝ} (d:CanonicalData H) (Q:E.Point) : H (-Q)=H Q := by
  have h := d.zsmul (-1) Q
  simpa using h

theorem canonical_torsion {H:E.Point→ℝ} (d:CanonicalData H) (U:E.Point) (hu:U+U=0) : H U=0 := by
  simpa [d.zero] using d.torsion 0 U hu

theorem classified_height {H:E.Point→ℝ} (d:CanonicalData H) (Q:E.Point)
    (h:Classified Q) : H Q=0 ∨ H Q=H R := by
  rcases h with ht|⟨U,hu,hp|hm⟩
  · exact Or.inl (canonical_torsion d Q ht)
  · right; rw [hp]; exact d.torsion R U hu
  · right; rw [hm,canonical_neg d]; exact d.torsion R U hu

/-- The exact integer comparison used by the saturation threshold. -/
theorem height_integer_comparison : (41:ℕ)^3*676*392^36<9^108 := by norm_num

theorem saturation_log_comparison :
    Real.log 41/36+Real.log 676/108+Real.log 392/3<Real.log 9 := by
  have hn : (41:ℝ)^3*676*392^36<9^108 := by exact_mod_cast height_integer_comparison
  have hl := Real.log_lt_log (by positivity : 0<(41:ℝ)^3*676*392^36) hn
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hl
  norm_num at hl
  linarith

/-- Saturation's small-height conclusion, derived from the explicit
canonical bounds and the actual equality 2R=P. -/
theorem small_height_of_large_index {H:E.Point→ℝ} (d:CanonicalData H)
    (G U:E.Point) (m:ℤ) (hu:U+U=0) (hm:R=m • G+U) (hm3:3≤|m|) :
    xHeight G<Real.log 9 := by
  have hR : H R=(m:ℝ)^2*H G := by rw [hm,d.torsion _ _ hu,d.zsmul]
  have hP : H P=4*H R := by rw [←two_zsmul_R,d.zsmul]; norm_num
  have hbound := d.upper P
  rw [d.heightP,hP] at hbound
  have hmreal : (3:ℝ)≤|(m:ℝ)| := by exact_mod_cast hm3
  have hsq : (9:ℝ)≤(m:ℝ)^2 := by nlinarith [sq_abs (m:ℝ)]
  have hg : 9*H G≤H R := by rw [hR]; nlinarith [d.nonneg G]
  have hsmall : xHeight G≤Real.log 41/36+Real.log 676/108+Real.log 392/3 := by
    linarith [d.lower G]
  exact hsmall.trans_lt saturation_log_comparison

end
end GlobalSaturationHeight318
