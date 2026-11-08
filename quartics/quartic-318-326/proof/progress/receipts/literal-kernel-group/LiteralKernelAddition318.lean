module
public import LiteralKernelScalar318
public section
noncomputable section
namespace LiteralKernelAddition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
@[expose] def product := pullback (structureMap N) (structureMap N)
@[expose] def productBase : product N ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)):=pullback.fst _ _ ≫ structureMap N
@[expose] def leftPoint : Points N (productBase N):=⟨pullback.fst _ _,rfl⟩
@[expose] def rightPoint : Points N (productBase N):=⟨pullback.snd _ _,pullback.condition.symm⟩
/-- The genuine kernel multiplication Scheme morphism, obtained from the
actual sum of the universal two kernel points. -/
@[expose] def addition : product N ⟶ K:=((leftPoint N)+(rightPoint N)).val
@[reassoc] theorem addition_base : addition N ≫ structureMap N=productBase N:=((leftPoint N)+(rightPoint N)).property
@[expose] def curvePair : product N ⟶ pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B):=
  LiteralSchemePointOperations318.pair N (productBase N) (intoCurve N _ (leftPoint N)) (intoCurve N _ (rightPoint N))
@[reassoc] theorem curvePair_fst : curvePair N ≫ pullback.fst _ _=pullback.fst (structureMap N) (structureMap N) ≫ inclusion N:=
  LiteralSchemePointOperations318.pair_fst N _ _ _
@[reassoc] theorem curvePair_snd : curvePair N ≫ pullback.snd _ _=pullback.snd (structureMap N) (structureMap N) ≫ inclusion N:=
  LiteralSchemePointOperations318.pair_snd N _ _ _
/-- Exact multiplication square with the original completed addition. -/
@[reassoc] theorem addition_inclusion : addition N ≫ inclusion N=curvePair N ≫ CompletedAddition318.addition A B hD:=
  LiteralKernelScalar318.add_inclusion N _ _ _

variable {T:Scheme} (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
@[expose] def pair (p q:Points N b) : T ⟶ product N:=pullback.lift p.val q.val (p.property.trans q.property.symm)
@[reassoc] theorem pair_fst (p q:Points N b) : pair N b p q ≫ pullback.fst _ _=p.val:=by simp [pair]
@[reassoc] theorem pair_snd (p q:Points N b) : pair N b p q ≫ pullback.snd _ _=q.val:=by simp [pair]
lemma pair_curve (p q:Points N b) : pair N b p q ≫ curvePair N=
    LiteralSchemePointOperations318.pair N b (intoCurve N b p) (intoCurve N b q):=by
  apply pullback.hom_ext
  · simp only [Category.assoc,curvePair_fst,pair_fst_assoc,LiteralSchemePointOperations318.pair_fst]
    rfl
  · simp only [Category.assoc,curvePair_snd,pair_snd_assoc,LiteralSchemePointOperations318.pair_snd]
    rfl
/-- Every Scheme test evaluates this exact Scheme multiplication as the
intrinsic kernel-group addition. -/
theorem addition_value (p q:Points N b) : pair N b p q ≫ addition N=(p+q).val:=by
  apply pullback.hom_ext
  · change (pair N b p q ≫ addition N) ≫ inclusion N=(p+q).val ≫ inclusion N
    rw [Category.assoc,addition_inclusion,←Category.assoc,pair_curve,LiteralKernelScalar318.add_inclusion]
  · change (pair N b p q ≫ addition N) ≫ structureMap N=(p+q).val ≫ structureMap N
    rw [Category.assoc,addition_base,(p+q).property,productBase,pair_fst_assoc,p.property]
end LiteralKernelAddition318
