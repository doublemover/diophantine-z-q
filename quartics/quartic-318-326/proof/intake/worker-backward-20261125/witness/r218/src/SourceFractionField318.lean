module
public import TensorFractionField318
public import ContactKummerOpenDomain318
public section
noncomputable section
namespace SourceFractionField318
open scoped TensorProduct
open ContactKummerOrder318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=KummerTensorField318.Raw (SourceKummerField318.parameter c)
local instance sourceField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceDomain : IsDomain (SourceOrder c):=source_domain c
local instance sourceFree : Module.Free R (SourceOrder c):=(source_finite_free c).2
local instance sourceAlgebra : Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra

@[expose] def genericEquiv : SourceOrder c⊗[R]K≃ₐ[SourceOrder c]L c :=
  { (Algebra.TensorProduct.comm R (SourceOrder c) K).toRingEquiv.trans (genericFiber c).toRingEquiv with
    commutes' := by intro x;rfl }

theorem actual_fractionField : IsFractionRing (SourceOrder c) (L c):=
  TensorFractionField318.fractionRing (genericEquiv c)

theorem embedding_on_polynomial (p:R) :
    embedding c (algebraMap R (SourceOrder c) p)=
      algebraMap K (L c) (algebraMap R K p) := by
  unfold embedding
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R K (K⊗[R]SourceOrder c)]
  exact (genericFiber c).commutes _
end SourceFractionField318
