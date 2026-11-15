module
public import ActualOriginalResidueLattice318
public import ActualOriginalFiniteRationalArc318
public section
noncomputable section
namespace ActualOriginalScaledCircle318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCongruenceCircle318
open ActualOriginalFiniteRationalArc318 ActualOriginalCompactFourier318
open ActualOriginalAffineInput318 ActualOriginalResiduePoisson318
open ActualOriginalTwistedWeight318 ActualOriginalResidueLattice318
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000

lemma actual_integer_equation_real (κ : ℤ) (x : Coordinates ℤ) :
    equation (κ : ℝ) (integerEmbed x) = (equation κ x : ℝ) :=
  equation_map (Int.castRingHom ℝ) κ x

/-- The scaled original phase is the genuine unit-circle Fourier
character at the original integer quadratic value. -/
lemma actual_scaled_weight_fourier (κ : ℤ) (β B : ℝ) (W : Coordinates ℝ → ℝ)
    (x : Coordinates ℤ) :
    scaledOriginalWeight (κ : ℝ) β B W (integerEmbed x) =
      (W (B⁻¹ • integerEmbed x) : ℂ) *
        fourier (equation κ x) (β : UnitAddCircle) := by
  unfold scaledOriginalWeight
  rw [actual_integer_equation_real,fourier_coe_apply]
  simp only [Complex.ofReal_one,div_one]
  congr 1
  push_cast
  congr 1
  ring

lemma actual_scaled_circle_summable (κ β B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    Summable (fun x : Coordinates ℤ => scaledOriginalWeight κ β B W (integerEmbed x)) := by
  let f := twistedWeight κ (β*B^2) W
  have hc := actual_affine_input_compact f
    (actual_twisted_weight_compact κ (β*B^2) W hWc) (0 : Coordinates ℝ) (inv_ne_zero hB)
  have hs := (actual_compact_lattice_norm_summable (affineInput f 0 B⁻¹) hc).of_norm
  simpa only [affineInput,zero_add,f,actual_scaled_twisted_identity κ β B hB W] using hs

@[expose] def scaledCircleSum (κ : ℤ) (β B : ℝ) (W : Coordinates ℝ → ℝ) : ℂ :=
  ∑' x : Coordinates ℤ, scaledOriginalWeight (κ : ℝ) β B W (integerEmbed x)

lemma actual_scaled_rational_phase (κ : ℤ) (q : ℕ) [NeZero q] (a : ℤ)
    (β B : ℝ) (W : Coordinates ℝ → ℝ) (x : Coordinates ℤ) :
    scaledOriginalWeight (κ : ℝ) ((a : ℝ)/(q : ℝ)+β) B W (integerEmbed x) =
      ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) (originalResidue q x)) *
        scaledOriginalWeight (κ : ℝ) β B W (integerEmbed x) := by
  rw [actual_scaled_weight_fourier,actual_scaled_weight_fourier,actual_original_rational_phase]
  ring

/-- Full rational-arc decomposition of the actual smooth compact original
sum. Each modular fiber is parametrized by precisely its integer translates,
using a proved global bijection and produced original summability. -/
theorem actual_scaled_rational_arc (κ : ℤ) (q : ℕ) [NeZero q] (a : ℤ)
    (β B : ℝ) (hB : B ≠ 0) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    scaledCircleSum κ ((a : ℝ)/(q : ℝ)+β) B W =
      ∑ r : Coordinates (ZMod q),
        ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r) *
          ∑' z : Coordinates ℤ, scaledOriginalWeight (κ : ℝ) β B W
            (integerEmbed (residueLift q r)+(q : ℝ) • integerEmbed z) := by
  unfold scaledCircleSum
  rw [actual_original_residue_tsum q _
    (actual_scaled_circle_summable (κ : ℝ) _ B hB W hW hWc)]
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [actual_scaled_rational_phase,actual_residue_point_class,actual_residue_point_embedding]
  exact tsum_mul_left

end ActualOriginalScaledCircle318
