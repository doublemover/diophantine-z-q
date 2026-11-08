module
public import CompletedAdditionCoefficient318
public import CompletedNegationCoefficient318
public import WeierstrassBaseChange318
public import LiteralSchemePointGroup318
public section
noncomputable section
namespace CoefficientSchemePoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "a" => algebraMap R S
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedAdditionCoefficient318.mapped_discriminant (S:=S) A B hD
local notation "pS" => WeierstrassGluing318.structureMap (a A) (a B)
local notation "c" => WeierstrassCoefficientMap318.coefficientMap (S:=S) A B
variable {T:Scheme} (b:T ⟶ Spec (CommRingCat.of S))

/-- The actual coefficient-changed family evaluated on arbitrary Scheme tests. -/
@[expose] def Points := {f:T ⟶ WeierstrassGluing318.scheme (a A) (a B) // f ≫ pS=b}
@[expose] def forget (p:Points N S b) : LiteralSchemePointOperations318.Points N (b ≫ Spec.map (CommRingCat.ofHom a)) :=
  ⟨p.val ≫ c,by rw [Category.assoc,WeierstrassCoefficientMap318.coefficientMap_base,←Category.assoc,p.property]⟩
theorem forget_injective : Function.Injective (forget N S b) := by
  intro p q h
  apply Subtype.ext
  apply (WeierstrassBaseChange318.coefficient_base_pullback (S:=S) A B).hom_ext
  · exact congrArg Subtype.val h
  · exact p.property.trans q.property.symm

@[expose] def lift (p:LiteralSchemePointOperations318.Points N (b ≫ Spec.map (CommRingCat.ofHom a))) : Points N S b :=
  ⟨(WeierstrassBaseChange318.coefficient_base_pullback (S:=S) A B).lift p.val b p.property,by simp⟩
@[simp] theorem forget_lift (p:LiteralSchemePointOperations318.Points N (b ≫ Spec.map (CommRingCat.ofHom a))) :
    forget N S b (lift N S b p)=p := by
  apply Subtype.ext
  exact (WeierstrassBaseChange318.coefficient_base_pullback (S:=S) A B).lift_fst p.val b p.property
@[simp] theorem lift_forget (p:Points N S b) : lift N S b (forget N S b p)=p := by
  apply forget_injective N S b
  exact forget_lift N S b _
/-- Both inverse identities use the actual coefficient pullback square. -/
@[expose] def equiv : Points N S b ≃ LiteralSchemePointOperations318.Points N (b ≫ Spec.map (CommRingCat.ofHom a)) where
  toFun:=forget N S b
  invFun:=lift N S b
  left_inv:=lift_forget N S b
  right_inv:=forget_lift N S b

@[expose] def zero : Points N S b := ⟨b ≫ WeierstrassGluing318.infinity (a A) (a B),by
  simp only [Category.assoc,WeierstrassGluing318.infinity_section,Category.comp_id]⟩
@[expose] def neg (p:Points N S b) : Points N S b := ⟨p.val ≫ GluedNegation318.negation (a A) (a B),by
  rw [Category.assoc,GluedNegation318.negation_over_base];exact p.property⟩
@[expose] def pair (p q:Points N S b) : T ⟶ pullback pS pS :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)
@[reassoc] theorem pair_fst (p q:Points N S b) : pair N S b p q ≫ pullback.fst _ _=p.val := by simp [pair]
@[reassoc] theorem pair_snd (p q:Points N S b) : pair N S b p q ≫ pullback.snd _ _=q.val := by simp [pair]
@[expose] def sum (p q:Points N S b) : Points N S b :=
  ⟨pair N S b p q ≫ CompletedAddition318.addition (a A) (a B) hS,by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pair_fst_assoc];exact p.property⟩

@[simp] theorem forget_zero : forget N S b (zero N S b)=LiteralSchemePointOperations318.zero N (b ≫ Spec.map (CommRingCat.ofHom a)) := by
  apply Subtype.ext
  change (b ≫ WeierstrassGluing318.infinity (a A) (a B)) ≫ c=_
  rw [Category.assoc,WeierstrassCoefficientMap318.coefficientMap_infinity,←Category.assoc]
  rfl
@[simp] theorem forget_neg (p:Points N S b) : forget N S b (neg N S b p)=
    LiteralSchemePointOperations318.neg N (b ≫ Spec.map (CommRingCat.ofHom a)) (forget N S b p) := by
  apply Subtype.ext
  change (p.val ≫ GluedNegation318.negation (a A) (a B)) ≫ c=(p.val ≫ c) ≫ GluedNegation318.negation A B
  rw [Category.assoc,←CompletedNegationCoefficient318.negation,←Category.assoc]
lemma pair_forget (p q:Points N S b) : pair N S b p q ≫ CompletedCoefficientProduct318.pair (S:=S) A B=
    LiteralSchemePointOperations318.pair N (b ≫ Spec.map (CommRingCat.ofHom a)) (forget N S b p) (forget N S b q) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedCoefficientProduct318.pair_fst,pair_fst_assoc,LiteralSchemePointOperations318.pair_fst]
    rfl
  · simp only [Category.assoc,CompletedCoefficientProduct318.pair_snd,pair_snd_assoc,LiteralSchemePointOperations318.pair_snd]
    rfl
@[simp] theorem forget_sum (p q:Points N S b) : forget N S b (sum N S b p q)=
    LiteralSchemePointOperations318.sum N (b ≫ Spec.map (CommRingCat.ofHom a)) (forget N S b p) (forget N S b q) := by
  apply Subtype.ext
  change (pair N S b p q ≫ CompletedAddition318.addition (a A) (a B) hS) ≫ c=_
  rw [Category.assoc,←CompletedAdditionCoefficient318.addition A B hD hS,←Category.assoc,pair_forget]
  rfl
end CoefficientSchemePoints318
