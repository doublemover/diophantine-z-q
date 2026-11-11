module
public import ActualTwoDescentGaloisEvenRootSigns318
public section
noncomputable section
namespace ActualTwoDescentGaloisHalfTranslations318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisRootHalf318
open ActualTwoDescentHalfFlipTranslations318 ActualTwoDescentHalvingCocycle318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_half_difference_zero (σ : GalQ) (n x : ℚ) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
    (hA : σ a=a) (hB : σ b=b) (hC : σ c=c) :
    halfDifference n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc) σ=0 := by
  rw [halfDifference,actual_galois_root_half]
  simp only [hA,hB,hC,sub_self]

lemma actual_half_difference_zero_torsion (σ : GalQ) (n x : ℚ) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
    (hA : σ a=a) (hB : σ b= -b) (hC : σ c= -c) :
    halfDifference n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc) σ=zeroTorsion _ (rational_parameter_ne n hn) := by
  rw [halfDifference,actual_galois_root_half]
  simp only [hA,hB,hC]
  rw [←actual_flip_zero_is_translation]
  abel

lemma actual_half_difference_first_torsion (σ : GalQ) (n x : ℚ) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
    (hA : σ a= -a) (hB : σ b=b) (hC : σ c= -c) :
    halfDifference n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc) σ=firstTorsion _ (rational_parameter_ne n hn) := by
  rw [halfDifference,actual_galois_root_half]
  simp only [hA,hB,hC]
  rw [←actual_flip_first_is_translation]
  abel

lemma actual_half_difference_last_torsion (σ : GalQ) (n x : ℚ) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
    (hA : σ a= -a) (hB : σ b= -b) (hC : σ c=c) :
    halfDifference n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc) σ=torsionPoint _ (rational_parameter_ne n hn) := by
  rw [halfDifference,actual_galois_root_half]
  simp only [hA,hB,hC]
  rw [←actual_flip_last_is_translation]
  abel

end ActualTwoDescentGaloisHalfTranslations318
