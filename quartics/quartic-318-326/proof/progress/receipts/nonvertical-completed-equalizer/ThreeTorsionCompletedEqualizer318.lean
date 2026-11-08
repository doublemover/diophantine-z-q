module
public import NonverticalCompletedDoubling318
public section
noncomputable section
namespace ThreeTorsionCompletedEqualizer318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NonverticalCompletedDoubling318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def doubling : Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B))⟶
    WeierstrassGluing318.scheme A B :=
  intoCompleted A B ≫ CompletedIteratedAddition318.doubling A B hD
@[expose] def negation : Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B))⟶
    WeierstrassGluing318.scheme A B := intoCompleted A B ≫ GluedNegation318.negation A B

/-- Cancellation uses the actual finite open immersion, not geometric points. -/
theorem condition_iff {X:Scheme} (f:X⟶Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B))) :
    f≫doubling A B hD=f≫negation A B ↔
      f≫ThreeTorsionEqualizerScheme318.doubling A B=f≫ThreeTorsionEqualizerScheme318.negation A B := by
  rw [doubling,negation,doubling_restriction,negation_restriction]
  rw [←Category.assoc,←Category.assoc,cancel_mono]

lemma condition : ThreeTorsionEqualizerScheme318.inclusion A B hD ≫ doubling A B hD =
    ThreeTorsionEqualizerScheme318.inclusion A B hD ≫ negation A B :=
  (condition_iff A B hD _).mpr (ThreeTorsionEqualizerScheme318.condition A B hD)

@[expose] def fork : Fork (doubling A B hD) (negation A B) :=
  Fork.ofι (ThreeTorsionEqualizerScheme318.inclusion A B hD) (condition A B hD)

/-- Universal property for actual global doubling and negation restricted to D(2y). -/
theorem universal {X:Scheme} (f:X⟶Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B)))
    (hf:f≫doubling A B hD=f≫negation A B) :
    ∃!g:X⟶ThreeTorsionScheme318.scheme A B hD,
      g≫ThreeTorsionEqualizerScheme318.inclusion A B hD=f :=
  ThreeTorsionEqualizerScheme318.universal A B hD f ((condition_iff A B hD f).mp hf)

/-- The existing rank-eight scheme is the categorical equalizer of these
actual completed-curve restrictions, for arbitrary Scheme test objects. -/
@[expose] def isLimit : IsLimit (fork A B hD) :=
  Fork.IsLimit.ofExistsUnique (fun s => universal A B hD s.ι s.condition)
end ThreeTorsionCompletedEqualizer318
