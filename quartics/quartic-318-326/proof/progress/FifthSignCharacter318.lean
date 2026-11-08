module
public import FifthSignGlobal318
public section
noncomputable section
namespace FifthSignCharacter318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthSourceInfinityCoordinates318 FifthSignAffine318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero L:=Algebra.charZero_of_charZero ℚ L
lemma raw_y_ne_zero:rawMap (ShortAffineJacobian318.y A B)≠0:=by
  rw [raw_y]
  apply mul_ne_zero
  · simpa only [map_zero] using (algebraMap ℚ L).injective.ne yScale.ne_zero
  · exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero (InfinityFieldCoordinates318.t_ne_zero units)))
      (CharacterRoot318.root_ne_zero _ _)
/-- The whole actual quotient is fixed only by positive full-character signs.
This is an equality of morphisms, not an inequality condition on a test point. -/
theorem fixed_iff (b:Fin 4→Bool):
    ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map=FifthCompletedGlobal318.map ↔ sign b=1:=by
  constructor
  · intro h
    have ho:=congrArg (fun f=>ContactProjectiveModel318.sourceOpen units≫f) h
    rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,FifthSignGlobal318.on_open] at ho
    change ContactGlobalSigns318.openMap units b≫(FifthSignGlobal318.affineMap≫WeierstrassGluing318.finiteChart A B)=
      FifthSignGlobal318.affineMap≫WeierstrassGluing318.finiteChart A B at ho
    rw [←Category.assoc] at ho
    have hm:ContactGlobalSigns318.openMap units b≫FifthSignGlobal318.affineMap=FifthSignGlobal318.affineMap:=
      (cancel_mono (WeierstrassGluing318.finiteChart A B)).mp ho
    unfold ContactGlobalSigns318.openMap FifthSignGlobal318.affineMap at hm
    rw [←Spec.map_comp] at hm
    have hy:=congrArg (fun f=>SourceOpenFractionField318.openEmbedding units (f.hom (ShortAffineJacobian318.y A B))) (Spec.map_injective hm)
    change SourceOpenFractionField318.openEmbedding units
      (ContactGlobalSigns318.openEquiv units b (FifthSourceOverlap318.shortMap (ShortAffineJacobian318.y A B)))=
      SourceOpenFractionField318.openEmbedding units (FifthSourceOverlap318.shortMap (ShortAffineJacobian318.y A B)) at hy
    rw [SourceSignFieldComparison318.open_embedding,FifthSignAffine318.open_embedding] at hy
    change sigma b (rawMap (ShortAffineJacobian318.y A B))=rawMap (ShortAffineJacobian318.y A B) at hy
    rcases sign_cases b with hp|hn
    · exact hp
    · rw [sigma_y_negative b hn] at hy
      have hz:(2:L)*rawMap (ShortAffineJacobian318.y A B)=0:=by linear_combination -hy
      exact False.elim (raw_y_ne_zero ((mul_eq_zero.mp hz).resolve_left (by norm_num)))
  · exact FifthSignGlobal318.positive b
/-- Actual target automorphism with explicit inverse, keeping elliptic
negation distinct from the degree-eight quotient map itself. -/
@[expose] def targetIso (b:Fin 4→Bool):WeierstrassGluing318.scheme A B≅WeierstrassGluing318.scheme A B:=by
  classical
  exact if sign b=-1 then GluedNegation318.negationIso A B else Iso.refl _
@[simp] theorem targetIso_hom (b:Fin 4→Bool):(targetIso b).hom=FifthSignGlobal318.targetAction b:=by
  unfold targetIso FifthSignGlobal318.targetAction
  split <;> rfl
@[simp] theorem targetIso_inv (b:Fin 4→Bool):(targetIso b).inv=FifthSignGlobal318.targetAction b:=by
  unfold targetIso FifthSignGlobal318.targetAction
  split <;> rfl
@[reassoc] theorem target_twice (b:Fin 4→Bool):FifthSignGlobal318.targetAction b≫FifthSignGlobal318.targetAction b=𝟙 _:=by
  simpa only [targetIso_hom,targetIso_inv] using (targetIso b).hom_inv_id
@[reassoc] theorem zero_fixed (b:Fin 4→Bool):WeierstrassGluing318.infinity A B≫FifthSignGlobal318.targetAction b=
    WeierstrassGluing318.infinity A B:=by
  unfold FifthSignGlobal318.targetAction
  split
  · exact GluedNegation318.infinity_fixed A B
  · exact Category.comp_id _
end FifthSignCharacter318
