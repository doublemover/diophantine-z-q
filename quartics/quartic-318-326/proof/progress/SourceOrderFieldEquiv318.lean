module
public import SourceOrderAutomorphisms318
public section
noncomputable section
namespace SourceOrderFieldEquiv318
open ContactKummerOrder318 SourceOrderAutomorphisms318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c

theorem extend_injective:Function.Injective (extend c):=by
  intro e f h
  ext x
  apply embedding_injective c
  have hx:=congrArg (fun g:L c≃ₐ[K]L c=>g (embedding c x)) h
  simpa only [extend_embedding] using hx

theorem extend_surjective:Function.Surjective (extend c):=by
  intro g
  let a:=SourceKummerField318.parameter c
  obtain ⟨b,hb⟩:=FourRootGalois318.signAutomorphism_surjective a
    ((AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)) g)
  refine ⟨SourceSignFieldComparison318.sourceEquiv c b,?_⟩
  rw [extend_sign]
  exact (AlgEquiv.autCongr (KummerTensorField318.rawEquiv a)).injective hb

theorem extend_mul (e f:SourceOrder c≃ₐ[R]SourceOrder c):
    extend c (e*f)=extend c e*extend c f:=by
  have hh:(extend c (e*f)).toRingHom=(extend c e*extend c f).toRingHom:=by
    apply IsFractionRing.ringHom_ext (A:=SourceOrder c)
    intro x
    change extend c (e*f) (embedding c x)=extend c e (extend c f (embedding c x))
    rw [extend_embedding,extend_embedding,extend_embedding]
    rfl
  ext x
  exact RingHom.congr_fun hh x

/-- The actual generic-fiber extension, as a full group equivalence.
This is not an abstract cardinality comparison. -/
@[expose] def fieldEquiv:(SourceOrder c≃ₐ[R]SourceOrder c)≃*(L c≃ₐ[K]L c):=
  { Equiv.ofBijective (extend c) ⟨extend_injective c,extend_surjective c⟩ with
    map_mul':=extend_mul c }
@[simp] theorem fieldEquiv_apply (e:SourceOrder c≃ₐ[R]SourceOrder c):
    fieldEquiv c e=extend c e:=rfl
end SourceOrderFieldEquiv318
