module
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Field.ZMod
public section
noncomputable section
namespace F3FrameChange318
set_option maxHeartbeats 650000
abbrev Standard:=Fin 2→ZMod 3
/-- The genuine general linear group of the standard two-dimensional F3
module, without a choice of labels for geometric torsion points. -/
abbrev Group:=Standard ≃ₗ[ZMod 3] Standard
@[expose] def standardBasis:=Pi.basisFun (ZMod 3) (Fin 2)
variable {V W:Type*} [AddCommGroup V] [Module (ZMod 3) V]
  [AddCommGroup W] [Module (ZMod 3) W]
@[expose] def linearize (v:Fin 2→V) : Standard →ₗ[ZMod 3] V:=
  standardBasis.constr (ZMod 3) v
@[simp] lemma linearize_basis (v:Fin 2→V) (i:Fin 2) : linearize v (standardBasis i)=v i:=
  standardBasis.constr_basis (ZMod 3) v i
/-- Right change of frame: the linear map specified by v is precomposed
with g. This convention fixes the later Scheme composition order. -/
@[expose] def change (g:Group) (v:Fin 2→V) (i:Fin 2) : V:=linearize v (g (standardBasis i))
lemma linearize_change (g:Group) (v:Fin 2→V) :
    linearize (change g v)=(linearize v).comp g.toLinearMap:=by
  apply standardBasis.ext
  intro i
  simp only [linearize_basis,change,LinearMap.comp_apply,LinearEquiv.coe_coe]
@[simp] theorem change_one (v:Fin 2→V) : change 1 v=v:=by
  funext i
  simp [change]
theorem change_mul (g h:Group) (v:Fin 2→V) : change h (change g v)=change (g*h) v:=by
  funext i
  simp only [change,linearize_change,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.mul_apply]
lemma linearize_natural (L:V →ₗ[ZMod 3] W) (v:Fin 2→V) :
    linearize (fun i=>L (v i))=L.comp (linearize v):=by
  apply standardBasis.ext
  intro i
  simp only [linearize_basis,LinearMap.comp_apply]
theorem change_natural (L:V →ₗ[ZMod 3] W) (g:Group) (v:Fin 2→V) (i:Fin 2) :
    L (change g v i)=change g (fun j=>L (v j)) i:=by
  simp only [change,linearize_natural,LinearMap.comp_apply]
theorem independent (g:Group) (v:Fin 2→V) (h:LinearIndependent (ZMod 3) v) :
    LinearIndependent (ZMod 3) (change g v):=by
  have hi:Function.Injective ((linearize v).comp g.toLinearMap):=
    (standardBasis.injective_constr_of_linearIndependent (R₂:=ZMod 3) h).comp g.injective
  change LinearIndependent (ZMod 3) (fun i=>((linearize v).comp g.toLinearMap) (standardBasis i))
  exact standardBasis.linearIndependent.map' ((linearize v).comp g.toLinearMap) (LinearMap.ker_eq_bot.mpr hi)
end F3FrameChange318
