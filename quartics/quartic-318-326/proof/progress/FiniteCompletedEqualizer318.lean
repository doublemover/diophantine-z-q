module
public import FiniteDoublingOpenLift318
public import ThreeTorsionCompletedEqualizer318
public import ThreeTorsionCompletedDoubling318
public section
noncomputable section
namespace FiniteCompletedEqualizer318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def doubling : ShortAffineScheme318.scheme A B ⟶ WeierstrassGluing318.scheme A B :=
  WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.doubling A B hD
@[expose] def negative : ShortAffineScheme318.scheme A B ⟶ WeierstrassGluing318.scheme A B :=
  WeierstrassGluing318.finiteChart A B ≫ GluedNegation318.negation A B

lemma condition : ThreeTorsionScheme318.inclusion A B hD ≫ doubling A B hD=
    ThreeTorsionScheme318.inclusion A B hD ≫ negative A B := by
  simpa only [doubling,negative,ThreeTorsionCompletedDoubling318.inclusion,Category.assoc] using
    ThreeTorsionCompletedDoubling318.doubling_eq_negation A B hD

/-- The D(2y) hypothesis is now a proved conclusion, so the entire original
rank-eight scheme is the equalizer on the whole finite chart. -/
theorem universal {X:Scheme} (f:X ⟶ ShortAffineScheme318.scheme A B)
    (hf:f ≫ doubling A B hD=f ≫ negative A B) :
    ∃!g:X ⟶ ThreeTorsionScheme318.scheme A B hD,g ≫ ThreeTorsionScheme318.inclusion A B hD=f := by
  have ho:f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.doubling A B hD=
      (f ≫ GluedNegation318.finiteNeg A B) ≫ WeierstrassGluing318.finiteChart A B := by
    simpa only [doubling,negative,GluedNegation318.finiteChart_negation,Category.assoc] using hf
  obtain ⟨k,hk,_⟩:=FiniteDoublingOpenLift318.universal A B hD f (f ≫ GluedNegation318.finiteNeg A B) ho
  have hc:k ≫ NonverticalCompletedDoubling318.intoCompleted A B=f ≫ WeierstrassGluing318.finiteChart A B := by
    rw [NonverticalCompletedDoubling318.intoCompleted,←Category.assoc,hk]
  have he:k ≫ ThreeTorsionCompletedEqualizer318.doubling A B hD=
      k ≫ ThreeTorsionCompletedEqualizer318.negation A B := by
    rw [ThreeTorsionCompletedEqualizer318.doubling,ThreeTorsionCompletedEqualizer318.negation,
      ←Category.assoc,←Category.assoc,hc]
    simpa only [doubling,negative,Category.assoc] using hf
  obtain ⟨g,hg,huniq⟩:=ThreeTorsionCompletedEqualizer318.universal A B hD k he
  refine ⟨g,?_,?_⟩
  · change g ≫ ThreeTorsionScheme318.inclusion A B hD=f
    rw [←ThreeTorsionEqualizerScheme318.inclusion_intoCurve,←Category.assoc,hg,hk]
  · intro g' hg'
    apply huniq
    apply (cancel_mono (ThreeTorsionEqualizerScheme318.openInclusion A B)).mp
    rw [Category.assoc,ThreeTorsionEqualizerScheme318.inclusion_intoCurve,hg',hk]

@[expose] def fork : Fork (doubling A B hD) (negative A B) :=
  Fork.ofι (ThreeTorsionScheme318.inclusion A B hD) (condition A B hD)
@[expose] def isLimit : IsLimit (fork A B hD) :=
  Fork.IsLimit.ofExistsUnique (fun s=>universal A B hD s.ι s.condition)
end FiniteCompletedEqualizer318
