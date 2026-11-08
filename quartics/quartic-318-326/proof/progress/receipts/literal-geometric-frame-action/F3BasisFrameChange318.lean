module
public import F3FrameChange318
public section
noncomputable section
namespace F3BasisFrameChange318
open F3FrameChange318
variable {V:Type*} [AddCommGroup V] [Module (ZMod 3) V]
@[expose] def frameEquiv (b:Module.Basis (Fin 2) (ZMod 3) V) : Standard ≃ₗ[ZMod 3] V:=
  standardBasis.equiv b (Equiv.refl _)
lemma frameEquiv_basis (b:Module.Basis (Fin 2) (ZMod 3) V) (i:Fin 2) :
    frameEquiv b (standardBasis i)=b i:=by
  simp [frameEquiv]
lemma linearize_eq (b:Module.Basis (Fin 2) (ZMod 3) V) : linearize b=(frameEquiv b).toLinearMap:=by
  apply standardBasis.ext
  intro i
  simp only [linearize_basis,LinearEquiv.coe_coe,frameEquiv_basis]
/-- The unique transition uses the two actual basis linear equivalences. -/
@[expose] def between (b c:Module.Basis (Fin 2) (ZMod 3) V) : F3FrameChange318.Group:=
  (frameEquiv c).trans (frameEquiv b).symm
@[simp] theorem change_between (b c:Module.Basis (Fin 2) (ZMod 3) V) :
    change (between b c) b=c:=by
  funext i
  simp only [change,linearize_eq,between,LinearEquiv.trans_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,frameEquiv_basis]
theorem unique (b c:Module.Basis (Fin 2) (ZMod 3) V) (g:F3FrameChange318.Group)
    (h:change g b=c) : g=between b c:=by
  apply standardBasis.ext'
  intro i
  apply (frameEquiv b).injective
  have hg:=congrFun h i
  have hc:=congrFun (change_between b c) i
  simpa only [change,linearize_eq,LinearEquiv.coe_coe] using hg.trans hc.symm
/-- Simple transitivity on genuine bases, without cardinality or a chosen
labeling of the underlying vector space. -/
theorem exists_unique (b c:Module.Basis (Fin 2) (ZMod 3) V) :
    ∃!g:F3FrameChange318.Group,change g b=c:=
  ⟨between b c,change_between b c,fun g hg=>unique b c g hg⟩
end F3BasisFrameChange318
