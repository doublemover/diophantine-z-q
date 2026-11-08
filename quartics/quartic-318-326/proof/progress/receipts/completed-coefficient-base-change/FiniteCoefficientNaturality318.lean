module
public import FiniteOutputCoefficient318
public import InfinityOutputCoefficient318
public section
noncomputable section
namespace FiniteCoefficientNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FinitePairCoefficient318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S

theorem chord (A B:R) :
    Spec.map (CommRingCat.ofHom (FiniteOutputCoefficient318.chord (S:=S) A B).toRingHom) ≫
      (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
    (RelativeChordScheme318.addition (a A) (a B) ≫ WeierstrassGluing318.finiteChart (a A) (a B)) ≫
      WeierstrassCoefficientMap318.coefficientMap A B := by
  rw [Category.assoc,WeierstrassCoefficientMap318.finite_coefficientMap,←Category.assoc,←Category.assoc]
  apply congrArg (fun f=>f ≫ WeierstrassGluing318.finiteChart A B)
  unfold RelativeChordScheme318.addition WeierstrassCoefficientMap318.finiteMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (FiniteOutputCoefficient318.chord_output (S:=S) A B))
theorem tangent (A B:R) :
    Spec.map (CommRingCat.ofHom (FiniteOutputCoefficient318.tangent (S:=S) A B).toRingHom) ≫
      (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
    (TangentOpenScheme318.addition (a A) (a B) ≫ WeierstrassGluing318.finiteChart (a A) (a B)) ≫
      WeierstrassCoefficientMap318.coefficientMap A B := by
  rw [Category.assoc,WeierstrassCoefficientMap318.finite_coefficientMap,←Category.assoc,←Category.assoc]
  apply congrArg (fun f=>f ≫ WeierstrassGluing318.finiteChart A B)
  unfold TangentOpenScheme318.addition WeierstrassCoefficientMap318.finiteMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (FiniteOutputCoefficient318.tangent_output (S:=S) A B))
theorem infinity (A B:R) (t:Bool) :
    Spec.map (CommRingCat.ofHom (InfinityOutputCoefficient318.map (S:=S) A B t).toRingHom) ≫
      InfinityAdditionScheme318.addition A B t=
    InfinityAdditionScheme318.addition (a A) (a B) t ≫ WeierstrassCoefficientMap318.coefficientMap A B := by
  rw [InfinityAdditionScheme318.addition,InfinityAdditionScheme318.addition,
    Category.assoc,WeierstrassCoefficientMap318.infinity_coefficientMap,←Category.assoc,←Category.assoc]
  apply congrArg (fun f=>f ≫ WeierstrassGluing318.infinityChart A B)
  unfold InfinityAdditionScheme318.chartAddition WeierstrassCoefficientMap318.infinityMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (InfinityOutputCoefficient318.output (S:=S) A B t))
theorem local_square (A B:R) (i:Fin 4) :
    Spec.map (CommRingCat.ofHom (localMap (S:=S) A B i).toRingHom) ≫ FiniteAdditionLocal318.localAddition A B i=
    FiniteAdditionLocal318.localAddition (a A) (a B) i ≫ WeierstrassCoefficientMap318.coefficientMap A B := by
  fin_cases i
  · exact chord A B
  · exact tangent A B
  · exact infinity A B false
  · exact infinity A B true

theorem cover_square (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) (i:Fin 4) :
    (FinitePairSchemeCover318.coordinateCover (a A) (a B) hS).f i ≫
      Spec.map (CommRingCat.ofHom (pair (S:=S) A B).toRingHom)=
    Spec.map (CommRingCat.ofHom (localMap (S:=S) A B i).toRingHom) ≫
      (FinitePairSchemeCover318.coordinateCover A B hD).f i := by
  change Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ Spec.map _=
    Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _))
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (localMap_base A B i x).symm

theorem coordinate (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    Spec.map (CommRingCat.ofHom (pair (S:=S) A B).toRingHom) ≫ FiniteAdditionGluing318.coordinateAddition A B hD=
      FiniteAdditionGluing318.coordinateAddition (a A) (a B) hS ≫ WeierstrassCoefficientMap318.coefficientMap A B := by
  apply (FinitePairSchemeCover318.coordinateCover (a A) (a B) hS).hom_ext
  intro i
  rw [←Category.assoc,cover_square A B hD hS,Category.assoc,
    FiniteAdditionGluing318.coordinate_restriction,←Category.assoc,
    FiniteAdditionGluing318.coordinate_restriction,local_square]
end FiniteCoefficientNaturality318
