module
public import ActualGaussianWeberHenselianPointMap318
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public section
noncomputable section

namespace ActualGaussianWeberPowerSeriesArc318

open IsLocalRing IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianChart318 ActualGaussianWeberHenselianPointMap318

variable (k : Type*) [Field k]

abbrev FormalField := LaurentSeries.RatFuncAdicCompl k
abbrev FormalValuation : ValuationSubring (FormalField k) :=
  (Polynomial.idealX k).adicCompletionIntegers (RatFunc k)

@[expose] def seriesEquiv : PowerSeries k ≃+* FormalValuation k :=
  LaurentSeries.powerSeriesRingEquiv k

@[expose] def parameter : FormalValuation k := seriesEquiv k PowerSeries.X

theorem parameter_ne : parameter k≠0 := by
  intro h
  exact PowerSeries.X_ne_zero ((seriesEquiv k).injective (h.trans (map_zero _).symm))

/-- The actual formal variable generates the maximal ideal in the
same valuation ring, transported from the stock formal power series. -/
theorem principal : maximalIdeal (FormalValuation k)=Ideal.span {parameter k} := by
  rw [←IsLocalRing.map_ringEquiv_maximalIdeal (seriesEquiv k),
      PowerSeries.maximalIdeal_eq_span_X,Ideal.map_span,Set.image_singleton] <;> rfl

theorem parameter_small : parameter k∈maximalIdeal (FormalValuation k) := by
  rw [principal k]
  exact Ideal.subset_span (by simp)

theorem formal_henselian : HenselianLocalRing (FormalValuation k) := by
  have hPS : IsAdicComplete (maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hFC := (IsAdicComplete.congr_ringEquiv (maximalIdeal (PowerSeries k)) (seriesEquiv k)).2 hPS
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hFC
  letI : IsAdicComplete (maximalIdeal (FormalValuation k)) (FormalValuation k) := hFC
  refine ⟨inferInstance,?_⟩
  intro f hf a ha hu
  exact HenselianRing.is_henselian f hf a ha (hu.map (Ideal.Quotient.mk _))

@[expose] def constVal : k→+*FormalValuation k :=
  (seriesEquiv k).toRingHom.comp PowerSeries.C

@[expose] def constField : k→+*FormalField k :=
  (FormalValuation k).subtype.comp (constVal k)

@[expose] def constantTerm : FormalValuation k→+*k :=
  PowerSeries.constantCoeff.comp (seriesEquiv k).symm.toRingHom

theorem constantTerm_const (c : k) : constantTerm k (constVal k c)=c := by
  change PowerSeries.constantCoeff ((seriesEquiv k).symm ((seriesEquiv k) (PowerSeries.C c)))=c
  rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_C]

theorem constantTerm_surjective : Function.Surjective (constantTerm k) :=
  fun c => ⟨constVal k c,constantTerm_const k c⟩

instance formal_residue_local : IsLocalHom (constantTerm k) :=
  IsLocalHom.of_surjective _ (constantTerm_surjective k)

/-- The actual residue identification, with its value on constants. -/
@[expose] def residueFormal : ResidueField (FormalValuation k) ≃+* k :=
  RingEquiv.ofBijective (ResidueField.lift (constantTerm k)) (by
    constructor
    · exact (ResidueField.lift (constantTerm k)).injective
    · intro r
      exact ⟨residue (FormalValuation k) (constVal k r),
        (ResidueField.lift_residue_apply _ _).trans (constantTerm_const k r)⟩)

theorem residueFormal_const (c : k) :
    residueFormal k (residue (FormalValuation k) (constVal k c))=c := by
  change ResidueField.lift (constantTerm k) (residue (FormalValuation k) (constVal k c))=c
  rw [ResidueField.lift_residue_apply,constantTerm_const]

theorem formal_two_ne (h2 : (2:k)≠0) : (2:FormalField k)≠0 := by
  intro h
  apply h2
  apply (constField k).injective
  simpa only [map_ofNat,map_zero] using h

theorem formal_residue_two_ne (h2 : (2:k)≠0) : (2:ResidueField (FormalValuation k))≠0 := by
  intro h
  apply h2
  simpa only [map_ofNat,map_zero] using congrArg (residueFormal k) h

/-- Actual stock point on the formal arc at infinity with exact
parameter t, not an assumed formal-group parametrization. -/
theorem formal_origin_arc (h2 : (2:k)≠0) :
    ∃ (x y : FormalField k), ∃ h : (curve (FormalField k)).toAffine.Nonsingular x y,
      specialize (FormalValuation k) (formal_residue_two_ne k h2) (Point.some x y h)=Point.zero ∧
      -x/y=(FormalValuation k).subtype (parameter k) := by
  letI := formal_henselian k
  let V := FormalValuation k
  let t := parameter k
  obtain ⟨w,⟨_,hW⟩,_⟩ := chart_exists t (parameter_small k)
  have ht : t≠0 := parameter_ne k
  have hw : w≠0 := by
    intro hw
    apply pow_ne_zero 3 ht
    have e : w+t*w^2=t^3 := hW
    simpa only [hw,zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero] using e.symm
  let T := V.subtype t
  let W := V.subtype w
  have hW0 : W≠0 :=
    fun h => hw (V.subtype_injective (h.trans (map_zero _).symm))
  have he : W+T*W^2=T^3 := by
    unfold identityChart at hW
    simpa only [map_add,map_pow,map_mul,T,W] using congrArg V.subtype hW
  let x := T/W
  let y := (-1)/W
  have hE : y^2=x^3-x := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hW0)
    have e₁ : y^2*W^3=W := by unfold y; field_simp [hW0] <;> ring
    have e₂ : (x^3-x)*W^3=T^3-T*W^2 := by unfold x; field_simp [hW0] <;> ring
    rw [e₁,e₂]
    linear_combination he
  have hx : x∉V := by
    intro H
    let z : V := ⟨x,H⟩
    have ee : z*t^2=1+t*w := by
      apply V.subtype_injective
      change x*T^2=1+T*W
      calc
        x*T^2=T^3/W := by unfold x; field_simp [hW0] <;> ring
        _ = 1+T*W := (div_eq_iff hW0).2 (by linear_combination -he)
    have ez := congrArg (residue V) ee
    have ht0 := (residue_eq_zero_iff t).2 (parameter_small k)
    simp only [map_add,map_mul,map_pow,map_one,ht0,
      zero_pow (by decide : (2:ℕ)≠0),zero_mul,mul_zero,add_zero] at ez
    exact zero_ne_one ez
  let h := nonsing_of_equation (formal_two_ne k h2) hE
  refine ⟨x,y,h,(specialize_some_eq_zero V (formal_residue_two_ne k h2) h).mpr hx,?_⟩
  unfold x y
  field_simp [hW0] <;> ring

end ActualGaussianWeberPowerSeriesArc318
