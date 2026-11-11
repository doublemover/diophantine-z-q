module
public import FourRootAllPrimeZeroSimple318
public import FourRootWholeInfinityDifferent318
public section
noncomputable section
namespace FourRootWholeZeroRadical318
open FourRootDerivativeZeroIdeals318 FourRootActualFractionField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
/-- The exact existing finite ideal is radical, detected by its actual
localizations at ALL maximal ideals. This does not assume the spectrum
consists of the known complex-valued points. -/
theorem finite_radical:(finiteIdeal b).IsRadical:=by
  apply Ideal.radical_eq_iff.mp
  apply Ideal.eq_of_localization_maximal
  intro p hp
  letI:p.IsMaximal:=hp
  rw [IsLocalization.map_radical p.primeCompl (Localization.AtPrime p)]
  rcases FourRootAllPrimeZeroSimple318.local_dichotomy b hb p with h|h
  · rw [h]
    simp
  · rw [h]
    exact (inferInstance:(IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrime).isRadical.radical
/-- The SAME whole infinity ideal is radical through the exact original
reciprocal polynomial-base isomorphism, retaining all infinity signs. -/
theorem infinity_radical:(infinityIdeal b).IsRadical:=by
  let e:=FourRootInfinityAffineComparison318.polynomialEquivalence b hb
  have h:((infinityIdeal b).map e.toRingHom).IsRadical:=by
    rw [FourRootWholeInfinityDifferent318.zero_ideal_image b hb]
    exact finite_radical (FourRootReciprocalBranchData318.branches b)
      (FourRootReciprocalBranchData318.branches_injective b hb)
  have hc:=h.comap e.toRingHom
  rw [Ideal.comap_map_of_bijective _ e.bijective] at hc
  exact hc
theorem finite_reduced:_root_.IsReduced ((A b)⧸finiteIdeal b):=by
  letI:(finiteIdeal b).IsRadical:=finite_radical b hb
  infer_instance
theorem infinity_reduced:_root_.IsReduced
    (FourRootInfinityCoordinateRing318.Ring b⧸infinityIdeal b):=by
  letI:(infinityIdeal b).IsRadical:=infinity_radical b hb
  infer_instance
end FourRootWholeZeroRadical318
