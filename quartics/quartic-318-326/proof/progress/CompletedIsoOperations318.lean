module
public import GluedNegation318
public import CompletedAddition318
public section
noncomputable section
namespace CompletedIsoOperations318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:Type u} [CommRing R] (A B:R)
variable {X:Scheme.{u}} (e:X≅(WeierstrassGluing318.scheme A B)) (p:X⟶Spec (CommRingCat.of R)) (he:e.hom≫(WeierstrassGluing318.structureMap A B)=p)

include he in
lemma inv_over_base:e.inv≫p=(WeierstrassGluing318.structureMap A B):=by rw [←he];simp

/-- The actual infinity section transported through the specified isomorphism. -/
@[expose] def zero:Spec (CommRingCat.of R)⟶X:=WeierstrassGluing318.infinity A B≫e.inv
@[reassoc] theorem zero_comparison:zero A B e≫e.hom=WeierstrassGluing318.infinity A B:=by simp [zero]
include he in
theorem zero_over_base:zero A B e≫p=𝟙 _:=by
  rw [zero,Category.assoc,inv_over_base A B e p he,WeierstrassGluing318.infinity_section]

/-- The actual whole-Scheme inverse, including infinity. -/
@[expose] def negation:X⟶X:=e.hom≫GluedNegation318.negation A B≫e.inv
@[reassoc] theorem negation_comparison:negation A B e≫e.hom=e.hom≫GluedNegation318.negation A B:=by simp [negation]
include he in
theorem negation_over_base:negation A B e≫p=p:=by
  rw [negation,Category.assoc,Category.assoc,inv_over_base A B e p he,
    GluedNegation318.negation_over_base,he]
theorem negation_twice:negation A B e≫negation A B e=𝟙 _:=by
  simp only [negation,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←Category.assoc (GluedNegation318.negation A B) (GluedNegation318.negation A B),
    GluedNegation318.negation_twice,Category.id_comp,Iso.hom_inv_id]
theorem zero_negation:zero A B e≫negation A B e=zero A B e:=by
  simp only [zero,negation,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←Category.assoc,GluedNegation318.infinity_fixed]

/-- The actual map between the two relative products. -/
@[expose] def pairMap:pullback p p⟶pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B):=
  pullback.lift (pullback.fst p p≫e.hom) (pullback.snd p p≫e.hom)
    (by simpa only [Category.assoc,he] using (pullback.condition (f:=p) (g:=p)))
@[reassoc] theorem pairMap_fst:pairMap A B e p he≫pullback.fst (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B)=pullback.fst p p≫e.hom:=by simp [pairMap]
@[reassoc] theorem pairMap_snd:pairMap A B e p he≫pullback.snd (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B)=pullback.snd p p≫e.hom:=by simp [pairMap]

/-- Actual multiplication morphism, not a transported set operation. -/
@[expose] def addition (hD:IsUnit (-16*(4*A^3+27*B^2))):pullback p p⟶X:=
  pairMap A B e p he≫CompletedAddition318.addition A B hD≫e.inv
@[reassoc] theorem addition_comparison (hD:IsUnit (-16*(4*A^3+27*B^2))):
    addition A B e p he hD≫e.hom=pairMap A B e p he≫CompletedAddition318.addition A B hD:=by
  simp [addition]
theorem addition_over_base (hD:IsUnit (-16*(4*A^3+27*B^2))):
    addition A B e p he hD≫p=pullback.fst p p≫p:=by
  rw [addition,Category.assoc,Category.assoc,inv_over_base A B e p he,
    CompletedAddition318.addition_over_base,←Category.assoc,pairMap_fst,Category.assoc,he]

variable {T:Scheme.{u}} (b:T⟶Spec (CommRingCat.of R))
@[expose] def Points:Type u:={f:T⟶X // f≫p=b}
@[expose] def TargetPoints:Type u:={f:T⟶(WeierstrassGluing318.scheme A B) // f≫(WeierstrassGluing318.structureMap A B)=b}
/-- Both directions preserve the actual base map on every Scheme test. -/
@[expose] def pointEquiv:Points p b≃TargetPoints A B b where
  toFun q:=⟨q.val≫e.hom,by rw [Category.assoc,he];exact q.property⟩
  invFun q:=⟨q.val≫e.inv,by rw [Category.assoc,inv_over_base A B e p he];exact q.property⟩
  left_inv q:=by apply Subtype.ext;simp
  right_inv q:=by apply Subtype.ext;simp
@[simp] theorem pointEquiv_val (q:Points p b):(pointEquiv A B e p he b q).val=q.val≫e.hom:=rfl
@[simp] theorem pointEquiv_symm_val (q:TargetPoints A B b):((pointEquiv A B e p he b).symm q).val=q.val≫e.inv:=rfl

@[expose] def pointZero:Points p b:=⟨b≫zero A B e,by rw [Category.assoc,zero_over_base A B e p he,Category.comp_id]⟩
@[expose] def pointNeg (q:Points p b):Points p b:=⟨q.val≫negation A B e,by
  rw [Category.assoc,negation_over_base A B e p he];exact q.property⟩
@[expose] def pointPair (q r:Points p b):T⟶pullback p p:=
  pullback.lift q.val r.val (q.property.trans r.property.symm)
@[expose] def pointSum (hD:IsUnit (-16*(4*A^3+27*B^2))) (q r:Points p b):Points p b:=
  ⟨pointPair p b q r≫addition A B e p he hD,by
    rw [Category.assoc,addition_over_base,←Category.assoc]
    simpa only [pointPair,pullback.lift_fst] using q.property⟩

@[simp] theorem pointZero_comparison:(pointEquiv A B e p he b (pointZero A B e p he b)).val=
    b≫WeierstrassGluing318.infinity A B:=by simp [pointZero,Category.assoc,zero_comparison]
@[simp] theorem pointNeg_comparison (q:Points p b):
    (pointEquiv A B e p he b (pointNeg A B e p he b q)).val=
      (pointEquiv A B e p he b q).val≫GluedNegation318.negation A B:=by
  simp [pointNeg,Category.assoc,negation_comparison]
@[reassoc] theorem pointPair_comparison (q r:Points p b):
    pointPair p b q r≫pairMap A B e p he=
      pullback.lift (q.val≫e.hom) (r.val≫e.hom)
        (by simp only [Category.assoc,he];exact q.property.trans r.property.symm):=by
  apply pullback.hom_ext <;> simp [Category.assoc,pairMap_fst,pairMap_snd,pointPair]
@[simp] theorem pointSum_comparison (hD:IsUnit (-16*(4*A^3+27*B^2))) (q r:Points p b):
    (pointEquiv A B e p he b (pointSum A B e p he b hD q r)).val=
      pullback.lift (q.val≫e.hom) (r.val≫e.hom)
        (by simp only [Category.assoc,he];exact q.property.trans r.property.symm)≫
        CompletedAddition318.addition A B hD:=by
  simp only [pointEquiv_val,pointSum,Category.assoc,addition_comparison]
  rw [←Category.assoc,pointPair_comparison]
end CompletedIsoOperations318
