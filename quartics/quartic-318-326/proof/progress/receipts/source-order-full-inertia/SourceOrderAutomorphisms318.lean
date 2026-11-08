module
public import SourceSignFieldComparison318
public import SourceFractionField318
public import ActualKummerGalois318
public section
noncomputable section
namespace SourceOrderAutomorphisms318
open ContactKummerOrder318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
/-- Extend the actual source-order automorphism by the literal rational
function base change and the existing exact generic-fiber equivalence. -/
@[expose] def extend (e:SourceOrder c≃ₐ[R]SourceOrder c):L c≃ₐ[K]L c:=
  (genericFiber c).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K) e).trans (genericFiber c))
lemma extend_embedding (e:SourceOrder c≃ₐ[R]SourceOrder c) (x:SourceOrder c):
    extend c e (embedding c x)=embedding c (e x):=by
  change genericFiber c ((Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K) e)
    ((genericFiber c).symm (genericFiber c (1⊗ₜ[R]x))))=genericFiber c (1⊗ₜ[R]e x)
  rw [AlgEquiv.symm_apply_apply,Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  rfl
lemma extend_sign (b:Fin 4→Bool):
    extend c (SourceSignFieldComparison318.sourceEquiv c b)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b:=by
  have hh:(extend c (SourceSignFieldComparison318.sourceEquiv c b)).toRingHom=
      (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom:=by
    apply IsFractionRing.ringHom_ext (A:=SourceOrder c)
    intro x
    change extend c (SourceSignFieldComparison318.sourceEquiv c b) (embedding c x)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b (embedding c x)
    rw [extend_embedding,SourceSignFieldComparison318.source_embedding]
  ext x
  exact RingHom.congr_fun hh x
lemma sign_injective:Function.Injective (SourceSignFieldComparison318.sourceEquiv c):=by
  intro b d h
  have he:=congrArg (extend c) h
  rw [extend_sign,extend_sign] at he
  exact FourRootAutomorphisms318.signEquiv_injective _ he
/-- Every Q[t]-algebra automorphism of the full original source order is
one of its literal sixteen root-sign automorphisms. -/
theorem sign_surjective:Function.Surjective (SourceSignFieldComparison318.sourceEquiv c):=by
  intro e
  let a:=SourceKummerField318.parameter c
  obtain ⟨b,hb⟩:=FourRootGalois318.signAutomorphism_surjective a
    ((AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)) (extend c e))
  have hs:FourRootAutomorphisms318.signEquiv a b=extend c e:=
    (AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)).injective hb
  refine ⟨b,?_⟩
  ext x
  apply embedding_injective c
  have hx:=congrArg (fun f:L c≃ₐ[K]L c=>f (embedding c x)) hs
  rw [←SourceSignFieldComparison318.source_embedding,extend_embedding] at hx
  exact hx
@[expose] def signEquiv:(Fin 4→Bool)≃(SourceOrder c≃ₐ[R]SourceOrder c):=
  Equiv.ofBijective _ ⟨sign_injective c,sign_surjective c⟩
theorem automorphism_card:Nat.card (SourceOrder c≃ₐ[R]SourceOrder c)=16:=by
  rw [←Nat.card_congr (signEquiv c)]
  simp
end SourceOrderAutomorphisms318
