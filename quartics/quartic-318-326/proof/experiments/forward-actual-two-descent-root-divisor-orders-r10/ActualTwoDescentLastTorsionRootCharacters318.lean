module
public import ActualTwoDescentLastTorsionGeometricHalf318
public section
noncomputable section
namespace ActualTwoDescentLastTorsionRootCharacters318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentHalfFlipTranslations318 ActualTwoDescentHalvingCocycle318
open ActualTwoDescentGaloisEvenRootSigns318 ActualTwoDescentGaloisHalfTranslations318
open ActualTwoDescentTorsionSignValues318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarRootCharacters318 ActualTwoDescentScalarRootIndependence318
open ActualTwoDescentLastTorsionGeometricHalf318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_last_torsion_root_characters (σ : GalQ) (n : ℚ) (hn : n ≠ 0)
    (u v : Qbar) (hun : u ≠ 0) (hvn : v ≠ 0) (hu : u^2=3) (hv : v^2= -algebraMap ℚ Qbar n) :
    torsionSignValue _ (rational_parameter_ne n hn)
      (halfDifference n hn (rootHalf _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
        (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1
        (actual_last_half_roots n u v hu hv).2.2) σ)=
      (scalarCharacter (Units.mk0 3 (by norm_num)) σ,scalarCharacter (Units.mk0 (-n) (neg_ne_zero.mpr hn)) σ) := by
  have hA := (actual_last_half_roots n u v hu hv).1
  have hB := (actual_last_half_roots n u v hu hv).2.1
  have hC := (actual_last_half_roots n u v hu hv).2.2
  have hu' : u^2=algebraMap ℚ Qbar (3 : ℚ) := by simpa only [map_ofNat] using hu
  have hv' : v^2=algebraMap ℚ Qbar (-n) := by simpa only [map_neg] using hv
  rcases actual_galois_root_sign σ 3 u hu' with hU|hU <;> rcases actual_galois_root_sign σ (-n) v hv' with hV|hV
  · rw [actual_half_difference_zero σ n (-3*n) hn (u*v) (2*v) 0 hA hB hC
      (by rw [map_mul,hU,hV]) (by rw [map_mul,map_ofNat,hV]) (map_zero σ),actual_sign_zero]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ u hun hu' σ,hU,div_self hun]; rfl
    · rw [actual_scalar_character_evaluate _ v hvn hv' σ,hV,div_self hvn]; rfl
  · rw [actual_half_difference_last_torsion σ n (-3*n) hn (u*v) (2*v) 0 hA hB hC
      (by rw [map_mul,hU,hV]; ring) (by rw [map_mul,map_ofNat,hV]; ring) (map_zero σ),actual_sign_last_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ u hun hu' σ,hU,div_self hun]; rfl
    · rw [actual_scalar_character_evaluate _ v hvn hv' σ,hV,neg_div,div_self hvn]; rfl
  · rw [actual_half_difference_first_torsion σ n (-3*n) hn (u*v) (2*v) 0 hA hB hC
      (by rw [map_mul,hU,hV]; ring) (by rw [map_mul,map_ofNat,hV]) (by simp only [map_zero,neg_zero]),actual_sign_first_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ u hun hu' σ,hU,neg_div,div_self hun]; rfl
    · rw [actual_scalar_character_evaluate _ v hvn hv' σ,hV,div_self hvn]; rfl
  · rw [actual_half_difference_zero_torsion σ n (-3*n) hn (u*v) (2*v) 0 hA hB hC
      (by rw [map_mul,hU,hV]; ring) (by rw [map_mul,map_ofNat,hV]; ring) (by simp only [map_zero,neg_zero]),actual_sign_zero_torsion]
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext
    · rw [actual_scalar_character_evaluate _ u hun hu' σ,hU,neg_div,div_self hun]; rfl
    · rw [actual_scalar_character_evaluate _ v hvn hv' σ,hV,neg_div,div_self hvn]; rfl

end ActualTwoDescentLastTorsionRootCharacters318
