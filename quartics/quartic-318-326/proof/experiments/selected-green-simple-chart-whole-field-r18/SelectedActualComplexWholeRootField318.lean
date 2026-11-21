module
public import SelectedWholeOrdinaryPath318
public import SelectedActualComplexOrdinaryScalar318
public import SelectedComplexOrdinaryOneField318
public section
noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedPrimitiveSameRootEvaluation318
open SelectedComplexOrdinaryBase318 SelectedComplexConnectedNoSplit318
open SelectedActualComplexOrdinaryScalar318

namespace SelectedActualComplexWholeRootField318

abbrev Period := {τ : UpperHalfPlane // OpenJComplexEvaluation318.Admissible τ}

@[expose] def periodMap (N : ℕ) [NeZero N] (τ : Period) : Ordinary × ℂ :=
  (⟨ActualQJ318.jInvariant τ.val,τ.property⟩,
    SelectedMarkedPeriodCoordinate318.arithmeticX N τ.val)

theorem periodMap_continuous (N : ℕ) [NeZero N] (hN : 1 < N) :
    Continuous (periodMap N) := by
  have h := continuousOn_iff_continuous_domRestrict.mp
    (SelectedWholeOrdinaryPath318.continuous_periodCoordinates N hN)
  have h₁ : Continuous (fun τ : Period => ActualQJ318.jInvariant τ.val) :=
    continuous_fst.comp h
  have h₂ : Continuous (fun τ : Period => SelectedMarkedPeriodCoordinate318.arithmeticX N τ.val) :=
    continuous_snd.comp h
  exact (h₁.subtype_mk (fun τ => τ.property)).prodMk h₂

variable (N : ℕ) [NeZero N] [IsFinite (kernelProjection N N)]
  [Etale (kernelProjection N N)]
variable (hN : 2 < N) (I : Ideal (D N))
variable (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I)))
variable (hb : primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I))
variable (he : intoAffine N N (by omega : 1 < N) =
  e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
variable (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
variable (hσ : σ.comp (q N I) = (q N I).comp (sign N))
variable (p : (R N)[X]) (ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ)
variable (hep : ep (AdjoinRoot.root p) = coordinate N I σ hσ)

include hN hb he hσ hep in
theorem returns_whole_root_set :
    Set.range (periodMap N) = roots (p.map (toComplex N)) := by
  ext z
  constructor
  · rintro ⟨τ,rfl⟩
    change (p.map (toComplex N)).eval₂
      (evaluation ⟨ActualQJ318.jInvariant τ.val,τ.property⟩)
      (SelectedMarkedPeriodCoordinate318.arithmeticX N τ.val) = 0
    rw [eval₂_map,evaluation_commutes]
    exact period_is_root N I e hb τ.val τ.property σ hσ p ep hep (by omega) he
  · intro hz
    have hz' : p.eval₂ ((evaluation z.1).comp (toComplex N)) z.2 = 0 := by
      change (p.map (toComplex N)).eval₂ (evaluation z.1) z.2 = 0 at hz
      rwa [eval₂_map] at hz
    let f : AdjoinRoot p →+* ℂ := AdjoinRoot.lift _ z.2 hz'
    obtain ⟨τ,hτ,hf⟩ := SelectedWholeOrdinaryPeriodEvaluation318.point_surjective
      N hN I e hb he σ hσ p ep hep f
    have hfJ : f (algebraMap (R N) (AdjoinRoot p) (OpenJModel318.jCoord N)) = z.1.val := by
      rw [f,AdjoinRoot.algebraMap_eq,AdjoinRoot.lift_of,RingHom.comp_apply,toComplex_j,evaluation_j]
    have hfx : f (AdjoinRoot.root p) = z.2 := AdjoinRoot.lift_root hz'
    refine ⟨⟨τ,hτ⟩,?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change ActualQJ318.jInvariant τ = z.1.val
      rw [← OpenJComplexEvaluation318.evaluation_jCoord N τ hτ,← rootEval_base N I e hb τ hτ σ p ep,
        hf,hfJ]
    · change SelectedMarkedPeriodCoordinate318.arithmeticX N τ = z.2
      rw [← rootEval_root N I e hb τ hτ σ hσ p ep hep (by omega) he,hf,hfx]

include hN hb he hσ hep in
theorem actual_simple_root_field (hp : p.Monic)
    (hder : IsUnit (AdjoinRoot.mk p p.derivative)) :
    IsField (AdjoinRoot (SelectedComplexOrdinaryOneField318.genericPolynomial
      (p.map (toComplex N)))) := by
  letI : PathConnectedSpace Period := isPathConnected_iff_pathConnectedSpace.mp
    SelectedActualAdmissiblePeriodPath318.admissible_pathConnected
  have hr : IsPathConnected (roots (p.map (toComplex N))) := by
    rw [← returns_whole_root_set N hN I e hb he σ hσ p ep hep]
    exact isPathConnected_range (periodMap_continuous N (by omega))
  have hdeg : 0 < (p.map (toComplex N)).natDegree := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hp1 : p.map (toComplex N) = 1 := ((hp.map _).natDegree_eq_zero).mp hd
    obtain ⟨z,hz⟩ := hr.nonempty
    change (p.map (toComplex N)).eval₂ (evaluation z.1) z.2 = 0 at hz
    rw [hp1,eval₂_one] at hz
    exact one_ne_zero hz
  apply SelectedComplexOrdinaryOneField318.generic_isField _ (hp.map _) hdeg hr.isConnected.isPreconnected
  intro z hz
  have hz' : p.eval₂ ((evaluation z.1).comp (toComplex N)) z.2 = 0 := by
    change (p.map (toComplex N)).eval₂ (evaluation z.1) z.2 = 0 at hz
    rwa [eval₂_map] at hz
  let f : AdjoinRoot p →+* ℂ := AdjoinRoot.lift _ z.2 hz'
  have hv := isUnit_iff_ne_zero.mp (hder.map f)
  rw [derivative_map,eval₂_map]
  simpa only [f,AdjoinRoot.lift_mk] using hv

end SelectedActualComplexWholeRootField318

#print axioms SelectedActualComplexWholeRootField318.returns_whole_root_set
#print axioms SelectedActualComplexWholeRootField318.actual_simple_root_field
