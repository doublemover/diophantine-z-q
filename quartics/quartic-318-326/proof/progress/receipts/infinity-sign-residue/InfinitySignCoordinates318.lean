module
public import InfinityOrderCoordinates318
public section
noncomputable section
namespace InfinitySignCoordinates318
open InfinityReciprocalAction318 InfinityOrderCoordinates318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
@[expose] def sign (b:Fin 4→Bool):Order c≃ₐ[Base c]Order c:=
  restrict c (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b)

theorem original_square (b:Fin 4→Bool) (x:Order c):
    InfinityOpenFractionField318.openEmbedding c (sign c b x)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b
        (InfinityOpenFractionField318.openEmbedding c x):=embedding_square c _ x

/-- The ramified coordinate changes by the zeroth original root sign. -/
theorem on_coordinate (b:Fin 4→Bool):
    sign c b (coordinate c)=if b 0 then -coordinate c else coordinate c:=by
  apply InfinityOpenFractionField318.openEmbedding_injective c
  rw [original_square,coordinate_embedding]
  simp only [InfinityFieldCoordinates318.u,InfinityFieldCoordinates318.constant,
    InfinityFieldCoordinates318.root,map_div₀,
    FourRootAutomorphisms318.signEquiv_generator]
  have hq:FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b
      (algebraMap ℚ (L c) (c 0:ℚ))=algebraMap ℚ (L c) (c 0:ℚ):=
    RingHom.map_rat_algebraMap (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom _
  rw [hq]
  cases hb:b 0 <;> simp [hb,map_neg,coordinate_embedding,InfinityFieldCoordinates318.u,
    InfinityFieldCoordinates318.constant,InfinityFieldCoordinates318.root,div_neg,neg_div]

/-- Each actual unit ratio carries the quotient of its original root sign
and the zeroth root sign. -/
theorem on_generator (b:Fin 4→Bool) (j:Fin 3):
    sign c b (generator c j)=
      if Bool.xor (b j.succ) (b 0) then -generator c j else generator c j:=by
  apply InfinityOpenFractionField318.openEmbedding_injective c
  rw [original_square,generator_embedding]
  simp only [InfinityFieldCoordinates318.ratio,InfinityFieldCoordinates318.root,map_div₀,
    FourRootAutomorphisms318.signEquiv_generator]
  cases hj:b j.succ <;> cases h0:b 0 <;>
    simp [hj,h0,map_neg,generator_embedding,InfinityFieldCoordinates318.ratio,
      InfinityFieldCoordinates318.root,div_neg,neg_div]

theorem twice (b:Fin 4→Bool) (x:Order c):sign c b (sign c b x)=x:=by
  apply InfinityOpenFractionField318.openEmbedding_injective c
  rw [original_square,original_square]
  exact congrArg (fun e:L c≃ₐ[K]L c=>e (InfinityOpenFractionField318.openEmbedding c x))
    (FourRootAutomorphisms318.signEquiv_trans_self (SourceKummerField318.parameter c) b)
end InfinitySignCoordinates318
