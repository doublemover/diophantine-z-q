module
public import BothMixedFiniteLocal318
public import ReversedBothMixedMaps318
public import BothMixedMaps318
public import MixedAdditionGluing318
public section
noncomputable section
namespace BothMixedWholeComparison318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The regular both-infinity law agrees with the whole mixed-input law under
literal input transitions over an arbitrary commutative coefficient algebra. -/
theorem direct_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (f:InfinityInputAlgebra318.PairRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=f (InfinityInputAlgebra318.u A B))
    (hv:φ (v1 A B)=f (InfinityInputAlgebra318.v A B))
    (hx:φ (u2 A B)*f (InfinityInputAlgebra318.y A B)=f (InfinityInputAlgebra318.x A B))
    (hy:φ (v2 A B)*f (InfinityInputAlgebra318.y A B)=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ MixedAdditionGluing318.coordinateAddition A B hD := by
  apply GenericFiniteCover318.comparison f (InfinityInputCover318.chartElement A B)
    (InfinityInputCover318.chart_span_top A B)
    (WeierstrassGluing318.scheme A B)
    (MixedAdditionGluing318.coordinateAddition A B hD)
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B)
    (MixedAdditionGluing318.localAddition A B hD)
  · intro i
    exact MixedAdditionGluing318.coordinate_restriction A B hD i
  · intro i
    let T:=Localization.Away (f (InfinityInputCover318.chartElement A B i))
    let g:S →ₐ[R] T:=IsScalarTower.toAlgHom R S T
    let ψ:=GenericFiniteCover318.lift f (InfinityInputCover318.chartElement A B i)
    have hp:=GenericFiniteCover318.lift_on_base f (InfinityInputCover318.chartElement A B i)
    rw [←Category.assoc,←Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (g.comp φ).toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ MixedAdditionGluing318.localAddition A B hD i
    fin_cases i
    · apply BothMixedFiniteLocal318.direct_agreement
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hu
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hv
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base,GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g hx
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hy
    · apply BothMixedMaps318.scheme_agreement
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hu
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hv
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base,GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g hx
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hy

/-- The regular both-infinity law agrees with the whole mixed-input law under
literal input transitions over an arbitrary commutative coefficient algebra. -/
theorem reversed_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (f:InfinityInputAlgebra318.PairRing A B →ₐ[R] S)
    (hu:φ (u2 A B)=f (InfinityInputAlgebra318.u A B))
    (hv:φ (v2 A B)=f (InfinityInputAlgebra318.v A B))
    (hx:φ (u1 A B)*f (InfinityInputAlgebra318.y A B)=f (InfinityInputAlgebra318.x A B))
    (hy:φ (v1 A B)*f (InfinityInputAlgebra318.y A B)=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ MixedAdditionGluing318.coordinateAddition A B hD := by
  apply GenericFiniteCover318.comparison f (InfinityInputCover318.chartElement A B)
    (InfinityInputCover318.chart_span_top A B)
    (WeierstrassGluing318.scheme A B)
    (MixedAdditionGluing318.coordinateAddition A B hD)
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B)
    (MixedAdditionGluing318.localAddition A B hD)
  · intro i
    exact MixedAdditionGluing318.coordinate_restriction A B hD i
  · intro i
    let T:=Localization.Away (f (InfinityInputCover318.chartElement A B i))
    let g:S →ₐ[R] T:=IsScalarTower.toAlgHom R S T
    let ψ:=GenericFiniteCover318.lift f (InfinityInputCover318.chartElement A B i)
    have hp:=GenericFiniteCover318.lift_on_base f (InfinityInputCover318.chartElement A B i)
    rw [←Category.assoc,←Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (g.comp φ).toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ MixedAdditionGluing318.localAddition A B hD i
    fin_cases i
    · apply BothMixedFiniteLocal318.reversed_agreement
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hu
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hv
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base,GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g hx
      · simp only [AlgHom.comp_apply,MixedInputLocal318.finiteInput,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hy
    · apply ReversedBothMixedMaps318.scheme_agreement
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hu
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply] using congrArg g hv
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base,GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul] using congrArg g hx
      · simp only [AlgHom.comp_apply,InfinityInputAlgebra318.pairMap,IsScalarTower.toAlgHom_apply]
        dsimp only [ψ,T]
        erw [GenericFiniteCover318.lift_on_base]
        simpa only [g,T,IsScalarTower.toAlgHom_apply,map_mul,map_one] using congrArg g hy

end BothMixedWholeComparison318
