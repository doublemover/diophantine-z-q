module
public import FiniteSymmetricCoordinates318
public import FiniteInfinitySymmetry318
public import FiniteAdditionLocal318
public section
noncomputable section
namespace FiniteLocalSymmetry318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
section Chord
open RelativeChordAlgebra318
theorem chord_scheme (A B:R) (φ ψ:ChordRing A B →ₐ[R] S)
    (hu:φ (x1 A B)=ψ (x2 A B)) (hv:φ (y1 A B)=ψ (y2 A B))
    (ht:φ (x2 A B)=ψ (x1 A B)) (hw:φ (y2 A B)=ψ (y1 A B)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ RelativeChordScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ RelativeChordScheme318.addition A B := by
  have hh:=FiniteSymmetricCoordinates318.chord_coordinates A B φ ψ hu hv ht hw
  have he:φ.comp (chordMap A B)=ψ.comp (chordMap A B) := by
    apply AffineEquationFunctor318.hom_ext
    · simpa only [AlgHom.comp_apply,chordMap_x] using hh.1
    · simpa only [AlgHom.comp_apply,chordMap_y] using hh.2
  dsimp only [RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
end Chord

section Tangent
open TangentOpenAlgebra318
theorem tangent_scheme (A B:R) (φ ψ:TangentRing A B →ₐ[R] S)
    (hu:φ (x1 A B)=ψ (x2 A B)) (hv:φ (y1 A B)=ψ (y2 A B))
    (ht:φ (x2 A B)=ψ (x1 A B)) (hw:φ (y2 A B)=ψ (y1 A B)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ TangentOpenScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ TangentOpenScheme318.addition A B := by
  have hh:=FiniteSymmetricCoordinates318.tangent_coordinates A B φ ψ hu hv ht hw
  have he:φ.comp (tangentMap A B)=ψ.comp (tangentMap A B) := by
    apply AffineEquationFunctor318.hom_ext
    · simpa only [AlgHom.comp_apply,tangentMap_x] using hh.1
    · simpa only [AlgHom.comp_apply,tangentMap_y] using hh.2
  dsimp only [TangentOpenScheme318.addition,TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
end Tangent

/-- Every one of the four actual local finite-input addition laws is invariant
under input exchange, over an arbitrary common coefficient algebra. -/
theorem scheme_agreement (A B:R) (i:Fin 4)
    (φ ψ:FiniteAdditionLocal318.LocalRing A B i →ₐ[R] S)
    (hp:∀r:RelativeChordAlgebra318.PairRing A B,
      φ (FiniteAdditionLocal318.inputMap A B i r)=
        ψ (FiniteAdditionLocal318.inputMap A B i (FinitePairSwap318.swap A B r))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ FiniteAdditionLocal318.localAddition A B i=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ FiniteAdditionLocal318.localAddition A B i := by
  have hu:=hp (InfinityAdditionAlgebra318.X1 A B)
  have hv:=hp (InfinityAdditionAlgebra318.Y1 A B)
  have ht:=hp (InfinityAdditionAlgebra318.X2 A B)
  have hw:=hp (InfinityAdditionAlgebra318.Y2 A B)
  rw [FinitePairSwap318.swap_X1] at hu
  rw [FinitePairSwap318.swap_Y1] at hv
  rw [FinitePairSwap318.swap_X2] at ht
  rw [FinitePairSwap318.swap_Y2] at hw
  fin_cases i
  · change _ ≫ (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
      _ ≫ (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    rw [←Category.assoc,←Category.assoc]
    exact congrArg (fun g => g ≫ WeierstrassGluing318.finiteChart A B) (chord_scheme A B φ ψ hu hv ht hw)
  · change _ ≫ (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
      _ ≫ (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    rw [←Category.assoc,←Category.assoc]
    exact congrArg (fun g => g ≫ WeierstrassGluing318.finiteChart A B) (tangent_scheme A B φ ψ hu hv ht hw)
  · exact FiniteInfinitySymmetry318.scheme_agreement A B false φ ψ hp
  · exact FiniteInfinitySymmetry318.scheme_agreement A B true φ ψ hp
end FiniteLocalSymmetry318
