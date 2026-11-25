module
public import TensorFractionField318
public import InfinityFieldEquivalence318
public import InfinityOpenChart318
public section
noncomputable section
namespace InfinityFractionField318
open scoped TensorProduct
open InfinityOpenChart318
set_option maxHeartbeats 800000
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev B:=InfinityFieldEquivalence318.B c
abbrev L:=InfinityFieldCoordinates318.L c
local instance infinityField : Field (B c):=(TripleQuadraticField318.infinity_field c).toField
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain : IsDomain (Order c):=order_domain c
local instance orderFree : Module.Free R (Order c):=(ThreeRootOrder318.finite_free _).2
local instance orderAlgebra : Algebra (Order c) (B c):=(embedding c).toAlgebra

@[expose] def genericEquiv : Order c⊗[R]K≃ₐ[Order c]B c :=
  { (Algebra.TensorProduct.comm R (Order c) K).toRingEquiv.trans (genericFiber c).toRingEquiv with
    commutes' := by intro x;rfl }

theorem infinity_fractionField : IsFractionRing (Order c) (B c):=
  TensorFractionField318.fractionRing (genericEquiv c)

@[expose] def originalEmbedding : Order c→+*L c:=
  (InfinityFieldEquivalence318.fieldEquiv c).toRingHom.comp (embedding c)
local instance originalAlgebra : Algebra (Order c) (L c):=(originalEmbedding c).toAlgebra

@[expose] def originalEquiv : B c≃ₐ[Order c]L c :=
  { InfinityFieldEquivalence318.fieldEquiv c with commutes' := by intro x;rfl }

/-- The unlocalized infinity order has the entire original contact field
as its fraction field under the actual recovered-coordinate embedding. -/
theorem original_fractionField : IsFractionRing (Order c) (L c) := by
  letI:=infinity_fractionField c
  exact IsFractionRing.of_algEquiv (originalEquiv c)

theorem originalEmbedding_injective : Function.Injective (originalEmbedding c) :=
  (InfinityFieldEquivalence318.fieldEquiv c).injective.comp (embedding_injective c)
end InfinityFractionField318
