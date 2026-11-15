module
public import ActualTwoDescentNonexceptionalGeometricRoots318
public section
noncomputable section
namespace ActualTwoDescentNonexceptionalRootCharacters318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentHalvingCocycle318 ActualTwoDescentHalfFlipTranslations318
open ActualTwoDescentGaloisEvenRootSigns318 ActualTwoDescentGaloisHalfTranslations318
open ActualTwoDescentTorsionSignValues318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarRootCharacters318 ActualTwoDescentScalarRootIndependence318
local instance : DecidableEq Qbar := Classical.decEq _

/-- The actual half-difference, in the ORIGINAL root basis, is exactly the two scalar root characters. -/
theorem actual_nonexceptional_root_character_pair (σ : GalQ) (n x y : ℚ) (hn : n ≠ 0)
    (hB : x-n ≠ 0) (hA : x+3*n ≠ 0) (a b c : Qbar)
    (han : a ≠ 0) (hbn : b ≠ 0) (hcn : c ≠ 0)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n) (hp : a*b*c= -algebraMap ℚ Qbar y) :
    torsionSignValue _ (rational_parameter_ne n hn)
      (halfDifference n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc) σ)=
      (scalarCharacter (Units.mk0 (x+3*n) hA) σ,scalarCharacter (Units.mk0 (x-n) hB) σ) := by
  have hbc : b^2=algebraMap ℚ Qbar ((Units.mk0 (x-n) hB : ℚˣ) : ℚ) := by simpa only [Units.val_mk0,map_sub] using hb
  have hcc : c^2=algebraMap ℚ Qbar ((Units.mk0 (x+3*n) hA : ℚˣ) : ℚ) := by
    simpa only [Units.val_mk0,map_add,map_mul,map_ofNat] using hc
  rcases actual_even_root_signs σ n x y a b c ha hb hc han hbn hcn hp with H|H|H|H
  · rw [actual_half_difference_zero σ n x hn a b c ha hb hc H.1 H.2.1 H.2.2,actual_sign_zero]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ c hcn hcc σ,H.2.2,div_self hcn]; rfl
    · rw [actual_scalar_character_evaluate _ b hbn hbc σ,H.2.1,div_self hbn]; rfl
  · rw [actual_half_difference_zero_torsion σ n x hn a b c ha hb hc H.1 H.2.1 H.2.2,actual_sign_zero_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ c hcn hcc σ,H.2.2,neg_div,div_self hcn]; rfl
    · rw [actual_scalar_character_evaluate _ b hbn hbc σ,H.2.1,neg_div,div_self hbn]; rfl
  · rw [actual_half_difference_first_torsion σ n x hn a b c ha hb hc H.1 H.2.1 H.2.2,actual_sign_first_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ c hcn hcc σ,H.2.2,neg_div,div_self hcn]; rfl
    · rw [actual_scalar_character_evaluate _ b hbn hbc σ,H.2.1,div_self hbn]; rfl
  · rw [actual_half_difference_last_torsion σ n x hn a b c ha hb hc H.1 H.2.1 H.2.2,actual_sign_last_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ c hcn hcc σ,H.2.2,div_self hcn]; rfl
    · rw [actual_scalar_character_evaluate _ b hbn hbc σ,H.2.1,neg_div,div_self hbn]; rfl

end ActualTwoDescentNonexceptionalRootCharacters318
