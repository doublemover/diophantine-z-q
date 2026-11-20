module
public import ActualMillerGeometricDivisor318
public import ActualTwoDescentOriginalTwoChartCubicScheme318
public import Mathlib.RingTheory.Nullstellensatz
import all ActualMillerRegularEvaluation318
import all ActualMillerAffineLocalChart318
import all ActualMillerAffineValuation318
import all ActualMillerGeometricDivisor318
import all ActualTwoDescentAffineChartCoordinates318
import all ActualTwoDescentInfinityLocalParameter318
import all ActualTwoDescentInfinityNativeDVR318
import all ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
import all ActualMillerInfinityChartMap318
import all ActualTwoDescentInfinityNativeFractionFunctions318
import all ActualTwoDescentOriginalTwoChartCubicScheme318
public section
noncomputable section

namespace ActualMillerClosedPointStalk318

open Polynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualMillerAffineLocalChart318 ActualMillerRegularEvaluation318
open ActualMillerAffineValuation318 ActualMillerGeometricDivisor318
open ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentInfinityNativeFractionFunctions318 ActualTwoDescentInfinityNativeDVR318

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- This is the literal surjection to the native affine chart, not a
different equation or a different affine surface. -/
def polynomialQuotient (n : K) : MvPolynomial (Fin 2) K →+* AffineChart n :=
  (AdjoinRoot.mk (curve n).toAffine.polynomial).comp
    (Polynomial.equivMvPolynomial K).symm.toRingEquiv.toRingHom

theorem polynomialQuotient_surjective (n : K) : Function.Surjective (polynomialQuotient n) :=
  (AdjoinRoot.mk_surjective (g := (curve n).toAffine.polynomial)).comp
    (Polynomial.equivMvPolynomial K).symm.surjective

private theorem eval_bivariate (c : Fin 2 → K) (p : Polynomial (Polynomial K)) :
    MvPolynomial.aeval c (Polynomial.equivMvPolynomial K p) =
      Polynomial.evalEval (c 0) (c 1) p := by
  let f : Polynomial (Polynomial K) →+* K :=
    (MvPolynomial.aeval c).toRingHom.comp (Polynomial.equivMvPolynomial K).toRingEquiv.toRingHom
  let g := Polynomial.evalEvalRingHom (c 0) (c 1)
  suffices h : f = g from DFunLike.congr_fun h p
  apply Polynomial.ringHom_ext
  · apply Polynomial.ringHom_ext
    · apply RingHom.ext
      intro a
      change MvPolynomial.aeval c (Polynomial.equivMvPolynomial K (C (C a))) =
        Polynomial.evalEval (c 0) (c 1) (C (C a))
      rw [Polynomial.equivMvPolynomial_C_C, Polynomial.evalEval_C, Polynomial.eval_C]
      simp
    · change MvPolynomial.aeval c (Polynomial.equivMvPolynomial K (C X)) =
        Polynomial.evalEval (c 0) (c 1) (C X)
      rw [Polynomial.equivMvPolynomial_C_X, Polynomial.evalEval_C, Polynomial.eval_X]
      simp
  · change MvPolynomial.aeval c (Polynomial.equivMvPolynomial K X) =
      Polynomial.evalEval (c 0) (c 1) X
    rw [Polynomial.equivMvPolynomial_X, Polynomial.evalEval_X]
    simp

/-- Every maximal ideal of the native affine cubic in algebraically
closed coefficients comes from its actual x,y evaluation. -/
theorem actual_affine_maximal_kernel [IsAlgClosed K] (n : K)
    (J : Ideal (AffineChart n)) (hJ : J.IsMaximal) :
    ∃ x y : K, ∃ he : (curve n).toAffine.Equation x y,
      J = pointKernel n x y he := by
  letI : J.IsMaximal := hJ
  have hpre : (J.comap (polynomialQuotient n)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (polynomialQuotient n) (polynomialQuotient_surjective n)
  obtain ⟨c, hc⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hpre
  have hmem (p : Polynomial (Polynomial K)) :
      AdjoinRoot.mk (curve n).toAffine.polynomial p ∈ J ↔
        Polynomial.evalEval (c 0) (c 1) p = 0 := by
    have h := MvPolynomial.mem_vanishingIdeal_singleton_iff
      (k := K) c (Polynomial.equivMvPolynomial K p)
    rw [← hc, eval_bivariate] at h
    change AdjoinRoot.mk (curve n).toAffine.polynomial
      ((Polynomial.equivMvPolynomial K).symm (Polynomial.equivMvPolynomial K p)) ∈ J ↔
        Polynomial.evalEval (c 0) (c 1) p = 0 at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h
  have he : (curve n).toAffine.Equation (c 0) (c 1) := by
    change Polynomial.evalEval (c 0) (c 1) (curve n).toAffine.polynomial = 0
    apply (hmem _).mp
    rw [AdjoinRoot.mk_self]
    exact J.zero_mem
  refine ⟨c 0, c 1, he, ?_⟩
  ext a
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [hmem]
  change _ ↔ AdjoinRoot.evalEval he (AdjoinRoot.mk _ p) = 0
  rw [AdjoinRoot.evalEval_mk]

abbrev affineSpectrum (n x y : K) (he : (curve n).toAffine.Equation x y) :
    PrimeSpectrum (AffineChart n) := ⟨pointKernel n x y he, inferInstance⟩

abbrev infinitySpectrum (n : K) : PrimeSpectrum (InfinityChart n) :=
  ⟨originIdeal n, (originIdealMaximal n).isPrime⟩

/-- The actual two original chart inclusions label the native points. -/
def schemePoint (n : K) : Point n → originalCubicScheme n
  | .zero => infinityChart n (infinitySpectrum n)
  | .some x y h => affineChart n (affineSpectrum n x y h.left)

/-- The two native charts cover the constructed pushout, not a model
identified only up to isomorphism. -/
theorem actual_charts_cover (n : K) (q : originalCubicScheme n) :
    (∃ a, affineChart n a = q) ∨ (∃ b, infinityChart n b = q) := by
  obtain ⟨i,p,hp⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoAffine n) (intoInfinity n)) q
  cases i with
  | none =>
    left
    refine ⟨intoAffine n p, ?_⟩
    change ((intoAffine n) ≫ affineChart n) p = q
    rw [show intoAffine n ≫ affineChart n =
      colimit.ι (span (intoAffine n) (intoInfinity n)) WalkingSpan.zero from
      colimit.w (span (intoAffine n) (intoInfinity n)) WalkingSpan.Hom.fst]
    exact hp
  | some j =>
    cases j with
    | left => exact Or.inl ⟨p,hp⟩
    | right => exact Or.inr ⟨p,hp⟩

private theorem infinity_in_overlap (n : K) (b : PrimeSpectrum (InfinityChart n))
    (hb : chartV n ∉ b.asIdeal) : ∃ p, intoInfinity n p = b := by
  change b ∈ Set.range (PrimeSpectrum.comap (algebraMap (InfinityChart n) (InfinityPuncture n)))
  rw [PrimeSpectrum.localization_away_comap_range (InfinityPuncture n) (chartV n)]
  exact hb

/-- Every closed point of the actual projective model in algebraically
closed coefficients is hit by a native point. The off-overlap
infinity branch uses the proved actual origin ideal equality. -/
theorem actual_closed_point_has_label [IsAlgClosed K] (n : K) (hn : n ≠ 0)
    (q : originalCubicScheme n) (hq : IsClosed ({q} : Set (originalCubicScheme n))) :
    ∃ P : Point n, schemePoint n P = q := by
  classical
  have finite (a : PrimeSpectrum (AffineChart n)) (ha : affineChart n a = q) :
      ∃ P : Point n, schemePoint n P = q := by
    have hc : IsClosed ({a} : Set (PrimeSpectrum (AffineChart n))) := by
      have h := hq.preimage (affineChart n).continuous
      rw [← ha] at h
      have hs : (affineChart n) ⁻¹' {affineChart n a} = ({a} : Set _) := by
        ext t
        change affineChart n t = affineChart n a ↔ t = a
        exact ⟨(affineChart n).isOpenEmbedding.injective, congrArg (affineChart n)⟩
      rwa [hs] at h
    obtain ⟨x,y,he,hx⟩ := actual_affine_maximal_kernel n a.asIdeal
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal a).mp hc)
    have hne : (curve n).toAffine.Nonsingular x y :=
      curve_nonsingular n x y hn ((curve_equation n x y).mp he)
    refine ⟨.some x y hne, ?_⟩
    change affineChart n (affineSpectrum n x y hne.left) = q
    have hpt : affineSpectrum n x y hne.left = a := by
      apply PrimeSpectrum.ext
      exact hx.symm
    rw [hpt, ha]
  rcases actual_charts_cover n q with ⟨a,ha⟩ | ⟨b,hb⟩
  · exact finite a ha
  · by_cases hV : chartV n ∈ b.asIdeal
    · letI : b.asIdeal.IsPrime := b.isPrime
      have hbO : b = infinitySpectrum n := by
        apply PrimeSpectrum.ext
        exact infinity_prime_off_overlap n _ hV
      exact ⟨.zero, by change infinityChart n (infinitySpectrum n) = q; rw [← hbO, hb]⟩
    · obtain ⟨p,hp⟩ := infinity_in_overlap n b hV
      apply finite (intoAffine n p)
      calc
        affineChart n (intoAffine n p) = infinityChart n (intoInfinity n p) :=
          congrArg (fun f : overlapScheme n ⟶ originalCubicScheme n => f p)
            (pushout.condition (f := intoAffine n) (g := intoInfinity n))
        _ = q := by rw [hp, hb]

/-- Exact pushout stalk map followed by Spec's canonical localization.
This does not need an abstract integral-scheme function field. -/
def chartStalkEquiv {A : Type u} [CommRing A] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum A) :
    X.presheaf.stalk (j p) ≃+* Localization.AtPrime p.asIdeal :=
  ((asIso (j.stalkMap p)) ≪≫ Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv

def affineStalkEquiv (n x y : K) (h : (curve n).toAffine.Nonsingular x y) :
    (originalCubicScheme n).presheaf.stalk (schemePoint n (.some x y h)) ≃+*
      AffineLocal n x y h.left :=
  chartStalkEquiv (affineChart n) (affineSpectrum n x y h.left)

def originStalkEquiv (n : K) :
    (originalCubicScheme n).presheaf.stalk (schemePoint n .zero) ≃+* InfinityLocalRing n :=
  chartStalkEquiv (infinityChart n) (infinitySpectrum n)

instance affine_stalk_domain (n x y : K) (h : (curve n).toAffine.Nonsingular x y) :
    IsDomain ((originalCubicScheme n).presheaf.stalk (schemePoint n (.some x y h))) :=
  Function.Injective.isDomain (affineStalkEquiv n x y h).toRingHom
    (affineStalkEquiv n x y h).injective

instance origin_stalk_domain (n : K) :
    IsDomain ((originalCubicScheme n).presheaf.stalk (schemePoint n .zero)) :=
  Function.Injective.isDomain (originStalkEquiv n).toRingHom (originStalkEquiv n).injective

theorem affine_stalk_isDVR (n x y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) :
    IsDiscreteValuationRing ((originalCubicScheme n).presheaf.stalk
      (schemePoint n (.some x y h))) := by
  letI := actual_affine_local_DVR n x y hn h.left
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (affineStalkEquiv n x y h).symm

theorem origin_stalk_isDVR (n : K) :
    IsDiscreteValuationRing ((originalCubicScheme n).presheaf.stalk (schemePoint n .zero)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (originStalkEquiv n).symm

/-- The fixed actual original function field receives each scheme stalk
through the very same normalized chart fraction-field map. These
embeddings do not choose a new rescaling of the Miller function. -/
def affineStalkIntoOriginal (n x y : K) (h : (curve n).toAffine.Nonsingular x y) :
    (originalCubicScheme n).presheaf.stalk (schemePoint n (.some x y h)) →+*
      OriginalFunctionField n :=
  (localFieldEquiv n x y h.left).symm.toRingHom.comp
    ((toLocalField n x y h.left).comp (affineStalkEquiv n x y h).toRingHom)

def originStalkIntoOriginal (n : K) :
    (originalCubicScheme n).presheaf.stalk (schemePoint n .zero) →+* OriginalFunctionField n :=
  (originalNativeFunctionFieldEquiv n).symm.toRingHom.comp
    ((infinityFractionMap n).comp (originStalkEquiv n).toRingHom)

theorem affine_stalk_on_chart (n x y : K) (h : (curve n).toAffine.Nonsingular x y)
    (a : AffineChart n) :
    affineStalkIntoOriginal n x y h
      ((affineStalkEquiv n x y h).symm (affineLocalMap n x y h.left a)) = fractionalBase n a := by
  change (localFieldEquiv n x y h.left).symm (toLocalField n x y h.left
    (affineStalkEquiv n x y h ((affineStalkEquiv n x y h).symm
      (affineLocalMap n x y h.left a)))) = fractionalBase n a
  rw [RingEquiv.apply_symm_apply, ← local_field_on_base, RingEquiv.symm_apply_apply]

theorem origin_stalk_on_chart (n : K) (a : InfinityChart n) :
    originalNativeFunctionFieldEquiv n (originStalkIntoOriginal n
      ((originStalkEquiv n).symm (algebraMap (InfinityChart n) (InfinityLocalRing n) a))) =
      chartFieldMap n a := by
  change originalNativeFunctionFieldEquiv n ((originalNativeFunctionFieldEquiv n).symm
    (infinityFractionMap n (originStalkEquiv n ((originStalkEquiv n).symm
      (algebraMap (InfinityChart n) (InfinityLocalRing n) a))))) = chartFieldMap n a
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] <;> rfl

/-- This map's target is the existing native function field, and its
source is the actual intrinsic stalk at the labelled point. -/
def stalkIntoOriginal (n : K) (R : Point n) :
    (originalCubicScheme n).presheaf.stalk (schemePoint n R) →+* OriginalFunctionField n :=
  match R with
  | .zero => originStalkIntoOriginal n
  | .some x y h => affineStalkIntoOriginal n x y h

def HasStalkOrder (n : K) (f : OriginalFunctionField n) (R : Point n) (k : ℤ) : Prop :=
  ∃ π : (originalCubicScheme n).presheaf.stalk (schemePoint n R), Irreducible π ∧
    ∃ e : ((originalCubicScheme n).presheaf.stalk (schemePoint n R))ˣ,
      f = stalkIntoOriginal n R (e : _) * (stalkIntoOriginal n R π)^k

/-- Transport a literal local unit and a uniformizer through the actual
chart map. In the origin branch the chosen parameter is still -X/Y. -/
theorem geometric_order_to_stalk (n : K) (f : OriginalFunctionField n)
    (R : Point n) (k : ℤ) (h : HasGeometricOrder n f R k) :
    HasStalkOrder n f R k := by
  cases R with
  | zero =>
    obtain ⟨e, he⟩ := h
    let j := originStalkEquiv n
    refine ⟨j.symm (-localU n),
      (MulEquiv.irreducible_iff (f := j.symm.toMulEquiv)).mpr
        (origin_parameter_irreducible n), e.map j.symm.toMonoidHom, ?_⟩
    apply (originalNativeFunctionFieldEquiv n).injective
    rw [map_mul, map_zpow]
    have h_e : originalNativeFunctionFieldEquiv n
      (originStalkIntoOriginal n (↑(e.map j.symm.toMonoidHom))) =
        infinityFractionMap n (e : InfinityLocalRing n) := by
      change originalNativeFunctionFieldEquiv n ((originalNativeFunctionFieldEquiv n).symm
        (infinityFractionMap n (j (j.symm (e : InfinityLocalRing n))))) = _
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    have h_t : originalNativeFunctionFieldEquiv n (originStalkIntoOriginal n (j.symm (-localU n))) =
        originT n := by
      change originalNativeFunctionFieldEquiv n ((originalNativeFunctionFieldEquiv n).symm
        (infinityFractionMap n (j (j.symm (-localU n))))) = -infinityFractionMap n (localU n)
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_neg]
    change originalNativeFunctionFieldEquiv n f = originalNativeFunctionFieldEquiv n
      (originStalkIntoOriginal n (↑(e.map j.symm.toMonoidHom))) *
      (originalNativeFunctionFieldEquiv n (originStalkIntoOriginal n (j.symm (-localU n))))^k
    rw [h_e, h_t]
    exact he
  | some x y hR =>
    obtain ⟨π, hπ, e, he⟩ := h
    let j := affineStalkEquiv n x y hR
    refine ⟨j.symm π, (MulEquiv.irreducible_iff (f := j.symm.toMulEquiv)).mpr hπ,
      e.map j.symm.toMonoidHom, ?_⟩
    apply (localFieldEquiv n x y hR.left).injective
    rw [map_mul, map_zpow]
    have hf (x₀ : AffineLocal n x y hR.left) :
        localFieldEquiv n x y hR.left (affineStalkIntoOriginal n x y hR (j.symm x₀)) =
          toLocalField n x y hR.left x₀ := by
      change localFieldEquiv n x y hR.left ((localFieldEquiv n x y hR.left).symm
        (toLocalField n x y hR.left (j (j.symm x₀)))) = _
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    change localFieldEquiv n x y hR.left f = localFieldEquiv n x y hR.left
      (affineStalkIntoOriginal n x y hR (j.symm (e : AffineLocal n x y hR.left))) *
      (localFieldEquiv n x y hR.left (affineStalkIntoOriginal n x y hR (j.symm π)))^k
    simp only [hf]
    exact he

/-- The exact one-step function has the claimed order in the actual
scheme stalk over every *closed* point, read at its native label.
No reciprocity, pairing, or divisor-class API is used. -/
theorem miller_order_at_actual_closed_point [IsAlgClosed K] [DecidableEq K]
    (n : K) (hn : n ≠ 0) (P Q : Point n) (q : originalCubicScheme n)
    (hq : IsClosed ({q} : Set (originalCubicScheme n))) :
    ∃ R : Point n, schemePoint n R = q ∧
      HasStalkOrder n (millerFunction n P Q) R (geometricDivisor n P Q R) := by
  obtain ⟨R, rfl⟩ := actual_closed_point_has_label n hn q hq
  exact ⟨R, rfl, geometric_order_to_stalk n _ R _ (geometric_divisor_agrees n hn P Q R)⟩

end ActualMillerClosedPointStalk318
