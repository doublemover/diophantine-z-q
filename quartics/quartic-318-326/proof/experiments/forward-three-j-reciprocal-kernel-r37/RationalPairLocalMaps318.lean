module
public import JLineOverlap318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace RationalPairLocalMaps318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (f g : ℚ[X])
abbrev NumeratorRing := Localization.Away f
abbrev DenominatorRing := Localization.Away g
@[expose] def numeratorInDenominator : DenominatorRing g := algebraMap ℚ[X] _ f
abbrev Common := Localization.Away (numeratorInDenominator f g)

@[expose] def numeratorBase : Spec (CommRingCat.of (NumeratorRing f)) ⟶
    Spec (CommRingCat.of ℚ[X]) := Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] _))
@[expose] def denominatorBase : Spec (CommRingCat.of (DenominatorRing g)) ⟶
    Spec (CommRingCat.of ℚ[X]) := Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] _))
instance numeratorBase_open : IsOpenImmersion (numeratorBase f) :=
  IsOpenImmersion.of_isLocalization f
instance denominatorBase_open : IsOpenImmersion (denominatorBase g) :=
  IsOpenImmersion.of_isLocalization g

@[expose] def denominatorInclusion : Spec (CommRingCat.of (Common f g)) ⟶
    Spec (CommRingCat.of (DenominatorRing g)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (DenominatorRing g) (Common f g)))
instance denominatorInclusion_open : IsOpenImmersion (denominatorInclusion f g) :=
  IsOpenImmersion.of_isLocalization (numeratorInDenominator f g)

/-- The genuine ring map from the numerator localization to the common
localization, constructed by its universal property. -/
@[expose] def toNumerator : NumeratorRing f →ₐ[ℚ] Common f g :=
  IsLocalization.Away.liftAlgHom
    (f:=IsScalarTower.toAlgHom ℚ ℚ[X] (Common f g)) f (by
      change IsUnit (algebraMap ℚ[X] (Common f g) f)
      rw [IsScalarTower.algebraMap_apply ℚ[X] (DenominatorRing g) (Common f g)]
      exact IsLocalization.Away.algebraMap_isUnit (numeratorInDenominator f g))

lemma toNumerator_on_base (a : ℚ[X]) :
    toNumerator f g (algebraMap ℚ[X] (NumeratorRing f) a) =
      algebraMap (DenominatorRing g) (Common f g) (algebraMap ℚ[X] (DenominatorRing g) a) := by
  simp only [toNumerator,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  exact IsScalarTower.algebraMap_apply ℚ[X] (DenominatorRing g) (Common f g) a

@[expose] def numeratorInclusion : Spec (CommRingCat.of (Common f g)) ⟶
    Spec (CommRingCat.of (NumeratorRing f)) :=
  Spec.map (CommRingCat.ofHom (toNumerator f g).toRingHom)

theorem base_square : denominatorInclusion f g ≫ denominatorBase g =
    numeratorInclusion f g ≫ numeratorBase f := by
  unfold denominatorInclusion denominatorBase numeratorInclusion numeratorBase
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (toNumerator_on_base f g a).symm

/-- The chosen common localization is the actual categorical intersection
of the two principal-open source charts. -/
theorem actual_pullback : IsPullback (numeratorInclusion f g) (denominatorInclusion f g)
    (numeratorBase f) (denominatorBase g) := by
  apply IsOpenImmersion.isPullback
  · exact base_square f g
  · have hf : (numeratorBase f).opensRange = PrimeSpectrum.basicOpen f := by
      apply TopologicalSpace.Opens.ext
      exact PrimeSpectrum.localization_away_comap_range _ _
    rw [hf]
    change PrimeSpectrum.basicOpen (numeratorInDenominator f g) =
      (denominatorInclusion f g).opensRange
    apply TopologicalSpace.Opens.ext
    exact (PrimeSpectrum.localization_away_comap_range _ _).symm

@[expose] def x : Common f g :=
  algebraMap (DenominatorRing g) _ (numeratorInDenominator f g)
@[expose] def y : Common f g :=
  algebraMap (DenominatorRing g) _ (algebraMap ℚ[X] (DenominatorRing g) g)
@[expose] def ix : Common f g := IsLocalization.Away.invSelf (numeratorInDenominator f g)
@[expose] def iy : Common f g :=
  algebraMap (DenominatorRing g) _ (IsLocalization.Away.invSelf g)

lemma x_ix : x f g * ix f g = 1 :=
  IsLocalization.Away.mul_invSelf (S:=Common f g) (numeratorInDenominator f g)
lemma y_iy : y f g * iy f g = 1 := by
  simpa only [y,iy,map_mul,map_one] using congrArg
    (algebraMap (DenominatorRing g) (Common f g))
    (IsLocalization.Away.mul_invSelf (S:=DenominatorRing g) g)

lemma toNumerator_inv : toNumerator f g (IsLocalization.Away.invSelf f) = ix f g := by
  have h := congrArg (toNumerator f g)
    (IsLocalization.Away.mul_invSelf (S:=NumeratorRing f) f)
  simp only [map_mul,map_one,toNumerator_on_base] at h
  change x f g * toNumerator f g (IsLocalization.Away.invSelf f) = 1 at h
  calc
    _ = (x f g * ix f g) * toNumerator f g (IsLocalization.Away.invSelf f) := by
      rw [x_ix,one_mul]
    _ = ix f g * (x f g * toNumerator f g (IsLocalization.Away.invSelf f)) := by ring
    _ = ix f g := by rw [h,mul_one]

@[expose] def forward : Common f g := x f g * iy f g
@[expose] def inverse : Common f g := y f g * ix f g
lemma forward_inverse : forward f g * inverse f g = 1 := by
  calc
    _ = (x f g * ix f g) * (y f g * iy f g) := by unfold forward inverse; ring
    _ = 1 := by rw [x_ix,y_iy,mul_one]

/-- On D(f), use the reciprocal target chart with coordinate g/f. -/
@[expose] def numeratorMap : Spec (CommRingCat.of (NumeratorRing f)) ⟶
    ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ)
    (algebraMap ℚ[X] (NumeratorRing f) g * IsLocalization.Away.invSelf f)).toRingHom) ≫
      JLineAtlas318.chart ℚ 0

/-- On D(g), use the finite target chart with coordinate f/g. -/
@[expose] def denominatorMap : Spec (CommRingCat.of (DenominatorRing g)) ⟶
    ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ)
    (algebraMap ℚ[X] (DenominatorRing g) f * IsLocalization.Away.invSelf g)).toRingHom) ≫
      JLineAtlas318.chart ℚ 1

/-- Equality of actual target scheme maps on the entire common localization,
using the explicit inverse pair, not equality on complex-valued points. -/
theorem projection_compatibility : numeratorInclusion f g ≫ numeratorMap f g =
    denominatorInclusion f g ≫ denominatorMap f g := by
  have hn : (toNumerator f g).toRingHom.comp
      (Polynomial.aeval (R:=ℚ)
        (algebraMap ℚ[X] (NumeratorRing f) g * IsLocalization.Away.invSelf f)).toRingHom =
      (Polynomial.aeval (R:=ℚ) (inverse f g)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_C,AlgHom.commutes]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_X,map_mul,toNumerator_on_base,toNumerator_inv,inverse,y]
  have hd : (algebraMap (DenominatorRing g) (Common f g)).comp
      (Polynomial.aeval (R:=ℚ)
        (algebraMap ℚ[X] (DenominatorRing g) f * IsLocalization.Away.invSelf g)).toRingHom =
      (Polynomial.aeval (R:=ℚ) (forward f g)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_C,←IsScalarTower.algebraMap_apply ℚ (DenominatorRing g) (Common f g)]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_X,map_mul,forward,x,iy,numeratorInDenominator]
  unfold numeratorInclusion numeratorMap denominatorInclusion denominatorMap
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((toNumerator f g).toRingHom.comp
    (Polynomial.aeval (R:=ℚ)
      (algebraMap ℚ[X] (NumeratorRing f) g * IsLocalization.Away.invSelf f)).toRingHom)) ≫
        JLineAtlas318.chart ℚ 0 =
    Spec.map (CommRingCat.ofHom ((algebraMap (DenominatorRing g) (Common f g)).comp
      (Polynomial.aeval (R:=ℚ)
        (algebraMap ℚ[X] (DenominatorRing g) f * IsLocalization.Away.invSelf g)).toRingHom)) ≫
          JLineAtlas318.chart ℚ 1
  rw [hn,hd]
  let u : (Common f g)ˣ :=
    ⟨forward f g,inverse f g,forward_inverse f g,by rw [mul_comm,forward_inverse]⟩
  exact (JLineOverlap318.unit_chart_overlap (R:=ℚ) u).symm

end RationalPairLocalMaps318
