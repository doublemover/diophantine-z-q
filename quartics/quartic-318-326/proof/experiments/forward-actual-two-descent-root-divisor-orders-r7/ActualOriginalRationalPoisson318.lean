module
public import ActualOriginalScaledCircle318
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public section
noncomputable section
namespace ActualOriginalRationalPoisson318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalTwistedWeight318 ActualOriginalCompactFourier318
open ActualOriginalAffineInput318 ActualOriginalAffineFourier318 ActualOriginalAffinePoisson318
open ActualOriginalResiduePoisson318 ActualOriginalResidueLattice318 ActualOriginalScaledCircle318
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000

@[expose] def completeArcCoefficient (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (m : Coordinates ℤ) : ℂ :=
  ∑ r : Coordinates (ZMod q),
    ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r) *
      (Real.fourierChar (frequency (integerEmbed m) (integerEmbed (residueLift q r))/(q : ℝ)) : ℂ)

lemma actual_residue_dual_summable (κ β : ℝ) (q : ℕ) (hq : 0 < q)
    (B : ℝ) (hB : 0 < B) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (r : Coordinates ℤ) :
    Summable (fun m : Coordinates ℤ =>
      (Real.fourierChar (frequency (integerEmbed m) (integerEmbed r)/(q : ℝ)) : ℂ) *
        ((B/(q : ℝ))^5 • originalCoordinateFourier κ (β*B^2) W
          ((B/(q : ℝ)) • integerEmbed m))) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := actual_original_affine_dual_summable (twistedWeight κ (β*B^2) W)
    (actual_twisted_weight_smooth κ (β*B^2) W hW)
    (actual_twisted_weight_compact κ (β*B^2) W hWc)
    (B⁻¹ • integerEmbed r) (R:=(q : ℝ)/B) (div_pos hqr hB)
  have he (m : Coordinates ℤ) :
      (Real.fourierChar (frequency (((q : ℝ)/B)⁻¹ • integerEmbed m) (B⁻¹ • integerEmbed r)) : ℂ) *
        ((((q : ℝ)/B)^5)⁻¹ • compactFourier (twistedWeight κ (β*B^2) W)
          (((q : ℝ)/B)⁻¹ • integerEmbed m)) =
      (Real.fourierChar (frequency (integerEmbed m) (integerEmbed r)/(q : ℝ)) : ℂ) *
        ((B/(q : ℝ))^5 • originalCoordinateFourier κ (β*B^2) W
          ((B/(q : ℝ)) • integerEmbed m)) := by
    rw [actual_residue_frequency (q : ℝ) B hqr.ne' hB.ne']
    simp only [inv_pow,inv_div]
    rfl
  simpa only [he] using hs.of_norm

/-- Exact rational-arc Poisson expansion of the SAME original scaled
circle sum. The complete finite coefficient ranges over all q^5 original
residues; finite/dual summation is exchanged only after actual summability. -/
theorem actual_original_rational_poisson (κ : ℤ) (q : ℕ) [NeZero q] (hq : 0 < q)
    (a : ℤ) (β B : ℝ) (hB : 0 < B) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    scaledCircleSum κ ((a : ℝ)/(q : ℝ)+β) B W =
      ∑' m : Coordinates ℤ, completeArcCoefficient κ q a m *
        ((B/(q : ℝ))^5 • originalCoordinateFourier (κ : ℝ) (β*B^2) W
          ((B/(q : ℝ)) • integerEmbed m)) := by
  classical
  let A (r : Coordinates (ZMod q)) : ℂ :=
    ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r)
  let D (r : Coordinates (ZMod q)) (m : Coordinates ℤ) : ℂ :=
    (Real.fourierChar (frequency (integerEmbed m) (integerEmbed (residueLift q r))/(q : ℝ)) : ℂ) *
      ((B/(q : ℝ))^5 • originalCoordinateFourier (κ : ℝ) (β*B^2) W
        ((B/(q : ℝ)) • integerEmbed m))
  have hs (r : Coordinates (ZMod q)) : Summable (fun m => A r * D r m) :=
    (actual_residue_dual_summable (κ : ℝ) β q hq B hB W hW hWc (residueLift q r)).mul_left (A r)
  rw [actual_scaled_rational_arc κ q a β B hB.ne' W hW hWc]
  simp_rw [actual_original_residue_poisson (κ : ℝ) β q hq B hB W hW hWc]
  change (∑ r : Coordinates (ZMod q), A r * ∑' m : Coordinates ℤ, D r m) = _
  calc
    _ = ∑ r : Coordinates (ZMod q), ∑' m : Coordinates ℤ, A r * D r m := by
      apply Finset.sum_congr rfl
      intro r hr
      exact tsum_mul_left.symm
    _ = ∑' m : Coordinates ℤ, ∑ r : Coordinates (ZMod q), A r * D r m :=
      (Summable.tsum_finsetSum (s:=Finset.univ) (fun r _ => hs r)).symm
    _ = _ := by
      apply tsum_congr
      intro m
      simp only [A,D,completeArcCoefficient,Finset.sum_mul,mul_assoc]

end ActualOriginalRationalPoisson318
