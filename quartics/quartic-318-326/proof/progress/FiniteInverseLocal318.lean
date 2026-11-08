module
public import FiniteAntiDiagonal318
import all WeierstrassGluing318
public section
noncomputable section
namespace FiniteInverseLocal318
open CategoryTheory AlgebraicGeometry
open FiniteAntiDiagonal318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R) (t:Bool)
local instance pairCommRing : CommRing (RelativeChordAlgebra318.PairRing A B):=inferInstance
local instance pairAlgebra : Algebra R (RelativeChordAlgebra318.PairRing A B):=inferInstance
abbrev Local:=Localization.Away (denominator A B t)
@[expose] def base : Curve A B→ₐ[R]Local A B t:=IsScalarTower.toAlgHom R _ _
@[expose] def toOutput : InfinityAdditionAlgebra318.OutputRing A B t→ₐ[R]Local A B t:=
  IsLocalization.Away.liftAlgHom (f:=(base A B t).comp (pair A B))
    (InfinityAdditionAlgebra318.numeratorY A B t)
    (IsLocalization.Away.algebraMap_isUnit (S:=Local A B t) (denominator A B t))

@[simp] lemma toOutput_pair (z:RelativeChordAlgebra318.PairRing A B) :
    toOutput A B t (InfinityAdditionAlgebra318.pairMap A B t z)=base A B t (pair A B z):=by
  simp only [toOutput,InfinityAdditionAlgebra318.pairMap,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.comp_apply]
  rfl
lemma output_denominator_zero :
    toOutput A B t (InfinityAdditionAlgebra318.pairMap A B t
      (InfinityAdditionAlgebra318.denominator A B t))=0:=by
  rw [toOutput_pair,denominator_zero,map_zero]

/-- Exact equality of the actual output coordinate map with the actual
infinity origin, over the whole anti-diagonal principal open. -/
lemma output_origin :
    (toOutput A B t).comp (InfinityAdditionAlgebra318.outputMap A B t)=
      (Algebra.ofId R (Local A B t)).comp (InfinityChart318.origin A B):=by
  apply InfinityChart318.hom_ext
  · simp only [AlgHom.comp_apply,InfinityAdditionAlgebra318.outputMap_x,
      InfinityChart318.origin_x,map_zero,InfinityAdditionAlgebra318.outX,
      map_mul,output_denominator_zero,mul_zero,zero_mul]
  · simp only [AlgHom.comp_apply,InfinityAdditionAlgebra318.outputMap_z,
      InfinityChart318.origin_z,map_zero,InfinityAdditionAlgebra318.outZ,
      map_mul,map_pow,output_denominator_zero,zero_pow (by decide : 3≠0),zero_mul]

/-- This is an equality of actual Scheme morphisms, not pointwise equality. -/
theorem scheme_inverse :
    Spec.map (CommRingCat.ofHom (toOutput A B t).toRingHom)≫
      InfinityAdditionScheme318.addition A B t=
    Spec.map (CommRingCat.ofHom (algebraMap R (Local A B t)))≫WeierstrassGluing318.infinity A B:=by
  have he:Spec.map (CommRingCat.ofHom (toOutput A B t).toRingHom)≫
      InfinityAdditionScheme318.chartAddition A B t=
      Spec.map (CommRingCat.ofHom (algebraMap R (Local A B t)))≫InfinitySmooth318.infinity A B:=by
    dsimp only [InfinityAdditionScheme318.chartAddition,InfinitySmooth318.infinity]
    rw [←Spec.map_comp,←Spec.map_comp]
    exact congrArg (fun f:InfinityChart318.Ring A B→ₐ[R]Local A B t=>
      Spec.map (CommRingCat.ofHom f.toRingHom)) (output_origin A B t)
  rw [InfinityAdditionScheme318.addition,←Category.assoc,he,Category.assoc,WeierstrassGluing318.infinity]
end FiniteInverseLocal318
