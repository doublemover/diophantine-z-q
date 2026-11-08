module
public import GenericFiniteCover318
public import BothFiniteLocal318
public import FiniteAdditionGluing318
public section
noncomputable section
namespace BothFiniteGlobalResolved318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Agreement with the complete finite-input law. The four local Scheme joins
are specialized to an actual localization cover of the common coefficient ring. -/
theorem scheme_agreement (A B:R) (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (φ : OutputRing A B →ₐ[R] S) (f : RelativeChordAlgebra318.PairRing A B →ₐ[R] S)
    (hu : φ (u1 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=f (InfinityAdditionAlgebra318.X1 A B))
    (hv : φ (v1 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=1)
    (ht : φ (u2 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=f (InfinityAdditionAlgebra318.X2 A B))
    (hw : φ (v2 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ FiniteAdditionGluing318.coordinateAddition A B hD := by
  apply GenericFiniteCover318.comparison f (FinitePairCover318.chartElement A B)
    (FinitePairCover318.chart_span_top A B hD)
    (WeierstrassGluing318.scheme A B)
    (FiniteAdditionGluing318.coordinateAddition A B hD)
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B)
    (FiniteAdditionLocal318.localAddition A B)
  · intro i
    exact FiniteAdditionGluing318.coordinate_restriction A B hD i
  · intro i
    let T := Localization.Away (f (FinitePairCover318.chartElement A B i))
    let g : S →ₐ[R] T := IsScalarTower.toAlgHom R S T
    let ψ := GenericFiniteCover318.lift f (FinitePairCover318.chartElement A B i)
    have hp := GenericFiniteCover318.lift_on_base f (FinitePairCover318.chartElement A B i)
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (g.comp φ).toRingHom) ≫ BothInfinityScheme318.addition A B =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ FiniteAdditionLocal318.localAddition A B i
    apply BothFiniteLocal318.scheme_agreement
    · simp only [AlgHom.comp_apply, FiniteAdditionLocal318.inputMap,
        FiniteAdditionLocal318.LocalRing, IsScalarTower.toAlgHom_apply]
      dsimp only [ψ]
      rw [GenericFiniteCover318.lift_on_base, GenericFiniteCover318.lift_on_base]
      simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g hu
    · simp only [AlgHom.comp_apply, FiniteAdditionLocal318.inputMap,
        FiniteAdditionLocal318.LocalRing, IsScalarTower.toAlgHom_apply]
      dsimp only [ψ]
      rw [GenericFiniteCover318.lift_on_base]
      simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hv
    · simp only [AlgHom.comp_apply, FiniteAdditionLocal318.inputMap,
        FiniteAdditionLocal318.LocalRing, IsScalarTower.toAlgHom_apply]
      dsimp only [ψ]
      rw [GenericFiniteCover318.lift_on_base, GenericFiniteCover318.lift_on_base]
      simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g ht
    · simp only [AlgHom.comp_apply, FiniteAdditionLocal318.inputMap,
        FiniteAdditionLocal318.LocalRing, IsScalarTower.toAlgHom_apply]
      dsimp only [ψ]
      rw [GenericFiniteCover318.lift_on_base]
      simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hw
end BothFiniteGlobalResolved318
