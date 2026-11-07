module
public import MixedDenominator318
public import FiniteCrossMaps318
public section
noncomputable section
namespace MixedCrossMaps318
open InfinityAdditionAlgebra318 InfinityAdditionFinite318
open RelativeChordAlgebra318 (PairRing)
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The first mixed overlap: actual chord-infinity and tangent-finite maps agree over every
common coefficient algebra. Their overlap automatically lies in the finite chord open. -/
theorem chord_infinity_tangent_finite (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (ψ:TangentOpenAlgebra318.TangentRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B false a)=ψ (TangentChordOverlap318.tangentPairMap A B a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B false=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ TangentOpenScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  have ht : IsUnit (ψ (TangentChordOverlap318.tangentPairMap A B (TangentOpenAlgebra318.ordinateSum A B))) :=
    (IsLocalization.Away.algebraMap_isUnit (S:=TangentOpenAlgebra318.TangentRing A B)
      (TangentOpenAlgebra318.ordinateSum A B)).map ψ
  rw [←hp] at ht
  have hd:=MixedDenominator318.actual_denominator_unit A B false φ ht
  rw [chord_agreement A B φ hd]
  have hpair (a:PairRing A B) : chordLift A B φ hd (TangentChordOverlap318.chordPairMap A B a)=
      ψ (TangentChordOverlap318.tangentPairMap A B a) := by rw [chordLift_pair,hp]
  rw [←Category.assoc,FiniteCrossMaps318.scheme_agreement A B (chordLift A B φ hd) ψ hpair,Category.assoc]

/-- The second mixed overlap, including any nilpotent coefficient directions. -/
theorem tangent_infinity_chord_finite (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (ψ:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B true a)=ψ (TangentChordOverlap318.chordPairMap A B a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B true=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ RelativeChordScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  have ht : IsUnit (ψ (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.gap A B))) :=
    (IsLocalization.Away.algebraMap_isUnit (S:=RelativeChordAlgebra318.ChordRing A B)
      (RelativeChordAlgebra318.gap A B)).map ψ
  rw [←hp] at ht
  have hd:=MixedDenominator318.actual_denominator_unit A B true φ ht
  rw [tangent_agreement A B φ hd]
  have hpair (a:PairRing A B) : ψ (TangentChordOverlap318.chordPairMap A B a)=
      tangentLift A B φ hd (TangentChordOverlap318.tangentPairMap A B a) := by rw [tangentLift_pair,hp]
  rw [←Category.assoc,←FiniteCrossMaps318.scheme_agreement A B ψ (tangentLift A B φ hd) hpair,Category.assoc]

/-- The same-family chord overlap for an arbitrary coefficient algebra map, rather than
only the canonical denominator lift. -/
theorem chord_infinity_chord_finite (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (ψ:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B false a)=ψ (TangentChordOverlap318.chordPairMap A B a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B false=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ RelativeChordScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  have hd : IsUnit (ψ (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.gap A B))) :=
    (IsLocalization.Away.algebraMap_isUnit (S:=RelativeChordAlgebra318.ChordRing A B)
      (RelativeChordAlgebra318.gap A B)).map ψ
  rw [←hp] at hd
  have he : chordLift A B φ hd=ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (RelativeChordAlgebra318.gap A B))
    apply AlgHom.ext
    intro a
    change chordLift A B φ hd (TangentChordOverlap318.chordPairMap A B a)=
      ψ (TangentChordOverlap318.chordPairMap A B a)
    rw [chordLift_pair,hp]
  rw [chord_agreement A B φ hd,he]

/-- The same-family tangent overlap in the same fully algebraic form. -/
theorem tangent_infinity_tangent_finite (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (ψ:TangentOpenAlgebra318.TangentRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B true a)=ψ (TangentChordOverlap318.tangentPairMap A B a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B true=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ TangentOpenScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  have hd : IsUnit (ψ (TangentChordOverlap318.tangentPairMap A B (TangentOpenAlgebra318.ordinateSum A B))) :=
    (IsLocalization.Away.algebraMap_isUnit (S:=TangentOpenAlgebra318.TangentRing A B)
      (TangentOpenAlgebra318.ordinateSum A B)).map ψ
  rw [←hp] at hd
  have he : tangentLift A B φ hd=ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (TangentOpenAlgebra318.ordinateSum A B))
    apply AlgHom.ext
    intro a
    change tangentLift A B φ hd (TangentChordOverlap318.tangentPairMap A B a)=
      ψ (TangentChordOverlap318.tangentPairMap A B a)
    rw [tangentLift_pair,hp]
  rw [tangent_agreement A B φ hd,he]

end MixedCrossMaps318
