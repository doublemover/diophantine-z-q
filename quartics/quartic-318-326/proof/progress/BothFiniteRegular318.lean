module
public import BothFiniteInfinity318
public import MixedCrossMaps318
public section
noncomputable section
namespace BothFiniteRegular318
open BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

@[expose] def infinityLift (A B:R) (tangent : Bool)
    (f : RelativeChordAlgebra318.PairRing A B →ₐ[R] S)
    (hY : IsUnit (f (InfinityAdditionAlgebra318.numeratorY A B tangent))) :
    InfinityAdditionAlgebra318.OutputRing A B tangent →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=f) (InfinityAdditionAlgebra318.numeratorY A B tangent) hY
@[simp] theorem infinityLift_pair (A B:R) (tangent : Bool)
    (f : RelativeChordAlgebra318.PairRing A B →ₐ[R] S)
    (hY : IsUnit (f (InfinityAdditionAlgebra318.numeratorY A B tangent)))
    (r : RelativeChordAlgebra318.PairRing A B) :
    infinityLift A B tangent f hY (InfinityAdditionAlgebra318.pairMap A B tangent r)=f r := by
  simp only [infinityLift,InfinityAdditionAlgebra318.pairMap,
    IsLocalization.Away.liftAlgHom_apply,IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl

lemma numerator_unit (A B:R) (tangent : Bool) (φ : OutputRing A B →ₐ[R] S)
    (f : RelativeChordAlgebra318.PairRing A B →ₐ[R] S)
    (hu : φ (u1 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=f (InfinityAdditionAlgebra318.X1 A B))
    (hv : φ (v1 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=1)
    (ht : φ (u2 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=f (InfinityAdditionAlgebra318.X2 A B))
    (hw : φ (v2 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=1)
    (hD : IsUnit (f (InfinityAdditionAlgebra318.denominator A B tangent))) :
    IsUnit (f (InfinityAdditionAlgebra318.numeratorY A B tangent)) := by
  apply isUnit_of_mul_isUnit_right (x:=φ (outV A B))
  rw [(BothFiniteMaps318.homogeneous_coordinates A B φ f tangent hu hv ht hw).2]
  exact hD.pow 3


/-- Actual both-infinity/finite-chord Scheme agreement under literal input transitions. -/
theorem chord_agreement (A B:R) (φ : OutputRing A B →ₐ[R] S)
    (ψ : RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (hu : φ (u1 A B)*ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.Y1 A B))=
      ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.X1 A B)))
    (hv : φ (v1 A B)*ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.Y1 A B))=1)
    (ht : φ (u2 A B)*ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.Y2 A B))=
      ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.X2 A B)))
    (hw : φ (v2 A B)*ψ (TangentChordOverlap318.chordPairMap A B (InfinityAdditionAlgebra318.Y2 A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ RelativeChordScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  let f := ψ.comp (TangentChordOverlap318.chordPairMap A B)
  have hD : IsUnit (f (InfinityAdditionAlgebra318.denominator A B false)) := by
    change IsUnit (ψ (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.gap A B)))
    exact (IsLocalization.Away.algebraMap_isUnit (S:=RelativeChordAlgebra318.ChordRing A B)
      (RelativeChordAlgebra318.gap A B)).map ψ
  let hY := numerator_unit A B false φ f hu hv ht hw hD
  let γ := infinityLift A B false f hY
  have hpair (r : RelativeChordAlgebra318.PairRing A B) :
      γ (InfinityAdditionAlgebra318.pairMap A B false r)=
        ψ (TangentChordOverlap318.chordPairMap A B r) := infinityLift_pair A B false f hY r
  have hh : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ InfinityAdditionScheme318.addition A B false := by
    apply BothFiniteInfinity318.scheme_agreement
    · simpa only [hpair] using hu
    · simpa only [hpair] using hv
    · simpa only [hpair] using ht
    · simpa only [hpair] using hw
  exact hh.trans (MixedCrossMaps318.chord_infinity_chord_finite A B γ ψ hpair)

/-- Actual both-infinity/finite-tangent Scheme agreement under literal input transitions. -/
theorem tangent_agreement (A B:R) (φ : OutputRing A B →ₐ[R] S)
    (ψ : TangentOpenAlgebra318.TangentRing A B →ₐ[R] S)
    (hu : φ (u1 A B)*ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.Y1 A B))=
      ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.X1 A B)))
    (hv : φ (v1 A B)*ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.Y1 A B))=1)
    (ht : φ (u2 A B)*ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.Y2 A B))=
      ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.X2 A B)))
    (hw : φ (v2 A B)*ψ (TangentChordOverlap318.tangentPairMap A B (InfinityAdditionAlgebra318.Y2 A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ TangentOpenScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  let f := ψ.comp (TangentChordOverlap318.tangentPairMap A B)
  have hD : IsUnit (f (InfinityAdditionAlgebra318.denominator A B true)) := by
    change IsUnit (ψ (TangentChordOverlap318.tangentPairMap A B (TangentOpenAlgebra318.ordinateSum A B)))
    exact (IsLocalization.Away.algebraMap_isUnit (S:=TangentOpenAlgebra318.TangentRing A B)
      (TangentOpenAlgebra318.ordinateSum A B)).map ψ
  let hY := numerator_unit A B true φ f hu hv ht hw hD
  let γ := infinityLift A B true f hY
  have hpair (r : RelativeChordAlgebra318.PairRing A B) :
      γ (InfinityAdditionAlgebra318.pairMap A B true r)=
        ψ (TangentChordOverlap318.tangentPairMap A B r) := infinityLift_pair A B true f hY r
  have hh : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ InfinityAdditionScheme318.addition A B true := by
    apply BothFiniteInfinity318.scheme_agreement
    · simpa only [hpair] using hu
    · simpa only [hpair] using hv
    · simpa only [hpair] using ht
    · simpa only [hpair] using hw
  exact hh.trans (MixedCrossMaps318.tangent_infinity_tangent_finite A B γ ψ hpair)

end BothFiniteRegular318
