module
public import LiteralKernelFunctor318
public section
noncomputable section
namespace LiteralKernelPointBaseTransport318
open AlgebraicGeometry CategoryTheory
open LiteralKernelSchemePoints318
variable (N:ℕ) {T:Scheme}
variable {b c:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))}
/-- Transport only across equality of actual base morphisms. The underlying
kernel map is unchanged; no arithmetic or geometric equivalence is assumed. -/
@[expose] def rebase (h:b=c) : Points N b ≃ₗ[ZMod 3] Points N c:=by
  subst c
  exact LinearEquiv.refl _ _
@[simp] theorem rebase_val (h:b=c) (p:Points N b) : (rebase N h p).val=p.val:=by
  subst c
  rfl
@[expose] def pull {U:Scheme} (f:U ⟶ T) (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
    (c:U ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))) (h:f ≫ b=c) :
    Points N b →ₗ[ZMod 3] Points N c:=
  (rebase N h).toLinearMap.comp (LiteralKernelFunctor318.precomposeLinear N b f)
@[simp] theorem pull_val {U:Scheme} (f:U ⟶ T) (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
    (c:U ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))) (h:f ≫ b=c) (p:Points N b) :
    (pull N f b c h p).val=f ≫ p.val:=by
  simp only [pull,LinearMap.comp_apply,LinearEquiv.coe_coe,rebase_val,LiteralKernelFunctor318.precomposeLinear_value]
end LiteralKernelPointBaseTransport318
