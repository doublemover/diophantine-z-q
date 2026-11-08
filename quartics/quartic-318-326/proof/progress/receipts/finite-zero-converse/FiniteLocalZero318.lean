module
public import InfinityOutputZero318
public import ChartInputEquality318
public import FiniteAdditionLocal318
import all WeierstrassGluing318
public section
noncomputable section
namespace FiniteLocalZero318
open AlgebraicGeometry CategoryTheory
open FiniteAdditionLocal318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

@[expose] def origin (A B:R) : InfinityChart318.Ring A B →ₐ[R] S :=
  (Algebra.ofId R S).comp (InfinityChart318.origin A B)
@[simp] lemma origin_x (A B:R) : origin (S:=S) A B (InfinityChart318.x A B)=0 := by
  simp only [origin,AlgHom.comp_apply,InfinityChart318.origin_x,map_zero]
@[simp] lemma origin_z (A B:R) : origin (S:=S) A B (InfinityChart318.z A B)=0 := by
  simp only [origin,AlgHom.comp_apply,InfinityChart318.origin_z,map_zero]
lemma origin_scheme (A B:R) :
    Spec.map (CommRingCat.ofHom (origin (S:=S) A B).toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B := by
  dsimp only [origin,WeierstrassGluing318.infinity,InfinitySmooth318.infinity,Spec.algebraMap]
  rw [←Category.assoc,←Spec.map_comp]
  rfl

/-- A finite affine output cannot be the infinity origin unless the test
algebra is the zero ring. This includes that case rather than excluding it. -/
theorem finite_zero_subsingleton (A B:R) (f:ShortAffineJacobian318.Ring A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart A B=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B) : Subsingleton S := by
  rw [←origin_scheme] at h
  have hz:=(ChartInputEquality318.finite_infinity A B f (origin A B) h).2
  rw [origin_z,zero_mul] at hz
  exact subsingleton_of_zero_eq_one hz

/-- Exact map identity on either infinity-output chart. -/
theorem infinity_zero (A B:R) (t:Bool) (φ:InfinityAdditionAlgebra318.OutputRing A B t →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B t=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B) :
    φ.comp (InfinityAdditionScheme318.rightInput A B t)=
      (φ.comp (InfinityAdditionScheme318.leftInput A B t)).comp (ChartNegation318.affineNeg A B) := by
  rw [←origin_scheme,InfinityAdditionScheme318.addition,←Category.assoc] at h
  change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (InfinityAdditionAlgebra318.outputMap A B t).toRingHom)) ≫ _=_ at h
  rw [←Spec.map_comp] at h
  have hm : φ.comp (InfinityAdditionAlgebra318.outputMap A B t)=origin A B :=
    ChartInputEquality318.infinity_injective A B _ _ h
  apply InfinityOutputZero318.input_maps
  · have hh:=congrArg (fun f:InfinityChart318.Ring A B →ₐ[R] S=>f (InfinityChart318.x A B)) hm
    simpa only [AlgHom.comp_apply,InfinityAdditionAlgebra318.outputMap_x,origin_x] using hh
  · have hh:=congrArg (fun f:InfinityChart318.Ring A B →ₐ[R] S=>f (InfinityChart318.z A B)) hm
    simpa only [AlgHom.comp_apply,InfinityAdditionAlgebra318.outputMap_z,origin_z] using hh

/-- All four actual finite-input addition charts satisfy the zero-sum
converse over every coefficient algebra, with no group axioms. -/
theorem input_maps (A B:R) (i:Fin 4) (φ:LocalRing A B i →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ localAddition A B i=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B) :
    (φ.comp (inputMap A B i)).comp (RelativeChordAlgebra318.rightPair A B)=
      ((φ.comp (inputMap A B i)).comp (RelativeChordAlgebra318.leftPair A B)).comp
        (ChartNegation318.affineNeg A B) := by
  fin_cases i
  · have hh:Spec.map (CommRingCat.ofHom (φ.comp (RelativeChordAlgebra318.chordMap A B)).toRingHom) ≫
        WeierstrassGluing318.finiteChart A B=Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B := by
      change _=(Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B)
      convert h using 1
      change Spec.map _ ≫ _=Spec.map _ ≫ (Spec.map _ ≫ _)
      rw [←Category.assoc,←Spec.map_comp]
      rfl
    letI:=finite_zero_subsingleton A B _ hh
    exact Subsingleton.elim _ _
  · have hh:Spec.map (CommRingCat.ofHom (φ.comp (TangentOpenAlgebra318.tangentMap A B)).toRingHom) ≫
        WeierstrassGluing318.finiteChart A B=Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B := by
      convert h using 1
      change Spec.map _ ≫ _=Spec.map _ ≫ (Spec.map _ ≫ _)
      rw [←Category.assoc,←Spec.map_comp]
      rfl
    letI:=finite_zero_subsingleton A B _ hh
    exact Subsingleton.elim _ _
  · exact infinity_zero A B false φ h
  · exact infinity_zero A B true φ h
end FiniteLocalZero318
