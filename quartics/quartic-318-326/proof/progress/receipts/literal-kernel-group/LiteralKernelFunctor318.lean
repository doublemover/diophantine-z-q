module
public import LiteralKernelAddition318
public section
noncomputable section
namespace LiteralKernelFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T U:Scheme}
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))) (f:U ⟶ T)
@[expose] def precompose (p:Points N b) : Points N (f ≫ b):=
  ⟨f ≫ p.val,by rw [Category.assoc,p.property]⟩
lemma precompose_pair (p q:Points N b) :
    LiteralKernelAddition318.pair N (f ≫ b) (precompose N b f p) (precompose N b f q)=
      f ≫ LiteralKernelAddition318.pair N b p q:=by
  apply pullback.hom_ext
  · rw [LiteralKernelAddition318.pair_fst,Category.assoc,LiteralKernelAddition318.pair_fst]
    rfl
  · rw [LiteralKernelAddition318.pair_snd,Category.assoc,LiteralKernelAddition318.pair_snd]
    rfl
@[simp] theorem precompose_zero : precompose N b f 0=0:=by
  apply Subtype.ext
  change f ≫ (0:Points N b).val=(0:Points N (f ≫ b)).val
  rw [LiteralKernelScalar318.zero_val,LiteralKernelScalar318.zero_val,Category.assoc]
@[simp] theorem precompose_add (p q:Points N b) :
    precompose N b f (p+q)=precompose N b f p+precompose N b f q:=by
  apply Subtype.ext
  change f ≫ (p+q).val=(precompose N b f p+precompose N b f q).val
  rw [←LiteralKernelAddition318.addition_value,←LiteralKernelAddition318.addition_value,
    precompose_pair,Category.assoc]
@[expose] def precomposeHom : Points N b →+ Points N (f ≫ b) where
  toFun:=precompose N b f
  map_zero':=precompose_zero N b f
  map_add':=precompose_add N b f
/-- Arbitrary Scheme precomposition is linear for the intrinsic kernel
F3 structure. This is the actual represented functor, not field-only data. -/
@[expose] def precomposeLinear : Points N b →ₗ[ZMod 3] Points N (f ≫ b):=
  (precomposeHom N b f).toZModLinearMap 3
@[simp] theorem precomposeLinear_value (p:Points N b) : (precomposeLinear N b f p).val=f ≫ p.val:=rfl
end LiteralKernelFunctor318
