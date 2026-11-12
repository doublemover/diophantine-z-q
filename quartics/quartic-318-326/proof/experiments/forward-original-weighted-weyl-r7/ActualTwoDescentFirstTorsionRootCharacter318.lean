module
public import ActualTwoDescentFirstTorsionGeometricHalf318
public section
noncomputable section
namespace ActualTwoDescentFirstTorsionRootCharacter318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentHalfFlipTranslations318 ActualTwoDescentHalvingCocycle318
open ActualTwoDescentGaloisEvenRootSigns318 ActualTwoDescentGaloisHalfTranslations318
open ActualTwoDescentTorsionSignValues318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarRootCharacters318 ActualTwoDescentScalarRootIndependence318
open ActualTwoDescentFirstTorsionGeometricHalf318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_first_torsion_root_character (σ : GalQ) (n : ℚ) (hn : n ≠ 0)
    (a : Qbar) (han : a ≠ 0) (ha : a^2=algebraMap ℚ Qbar n) :
    torsionSignValue _ (rational_parameter_ne n hn)
      (halfDifference n hn (rootHalf _ _ a 0 (2*a) (rational_parameter_ne n hn) ha
        (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2) σ)=
      (scalarCharacter (Units.mk0 n hn) σ,1) := by
  have hB := (actual_first_half_roots n hn a ha).1
  have hC := (actual_first_half_roots n hn a ha).2
  rcases actual_galois_root_sign σ n a ha with h|h
  · rw [actual_half_difference_zero σ n n hn a 0 (2*a) ha hB hC h (map_zero σ)
      (by rw [map_mul,map_ofNat,h]),actual_sign_zero]
    apply Prod.ext
    · apply Subtype.ext; apply Units.ext
      rw [actual_scalar_character_evaluate _ a han ha σ,h,div_self han]; rfl
    · rfl
  · rw [actual_half_difference_first_torsion σ n n hn a 0 (2*a) ha hB hC h (map_zero σ)
      (by rw [map_mul,map_ofNat,h]; ring),actual_sign_first_torsion]
    apply Prod.ext
    · apply Subtype.ext; apply Units.ext
      rw [actual_scalar_character_evaluate _ a han ha σ,h,neg_div,div_self han]; rfl
    · rfl

end ActualTwoDescentFirstTorsionRootCharacter318
