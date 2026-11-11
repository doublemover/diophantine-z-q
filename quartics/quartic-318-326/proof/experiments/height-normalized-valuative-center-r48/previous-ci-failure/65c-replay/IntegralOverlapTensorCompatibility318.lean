module
public import IntegralOverlapCoefficientRestrictions318
public import VerticalSection318
public section
noncomputable section
namespace IntegralOverlapTensorCompatibility318
open IntegralInfinityCommonBase318 IntegralOverlapCoefficients318
open IntegralOverlapChartMaps318 IntegralOverlapCoefficientRestrictions318
open IntegralReciprocalTensorIdentity318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

local instance overlapCommRing : CommRing (Overlap R c) := inferInstance
local instance overlapAlgebra : Algebra R (Overlap R c) := inferInstance
local instance finiteCommRing : CommRing (IntegralBranchCoordinates318.B R c 0) := inferInstance
local instance infinityCommRing : CommRing (IntegralInfinityChart318.Order R c) := inferInstance

local instance overlapCotangentModule :
    Module (Overlap R c) (KaehlerDifferential R (Overlap R c)) :=
  nativeCotangentModule R (Overlap R c)

@[expose] def finiteDifferential : KaehlerDifferential R (Overlap R c) :=
  AlgHomDifferential318.map (finiteMap R c)
    (KaehlerDifferential.D R (IntegralBranchCoordinates318.B R c 0)
      (IntegralBranchCoordinates318.sourceCoordinate R c 0))
@[expose] def infinityDifferential : KaehlerDifferential R (Overlap R c) :=
  AlgHomDifferential318.map (infinityMap R c)
    (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
      (IntegralInfinityChart318.coordinate R c))

/-- The exact derivative map of the actual overlap inclusion is used on
both charts. The coefficient is the signed reciprocal Jacobian. -/
theorem differential_transition : finiteDifferential R c =
    commonMap R c (derivativeFactor R c) • infinityDifferential R c := by
  rw [finiteDifferential,infinityDifferential,
    AlgHomDifferential318.map_D,AlgHomDifferential318.map_D,
    finite_coordinate,infinity_coordinate]
  have hyu := congrArg (commonMap R c).toRingHom (reciprocal_relation R c)
  rw [map_mul] at hyu
  change commonMap R c (rootUnit R c : CommonBase R c) *
    commonMap R c (reciprocalUnit R c : CommonBase R c)=
    commonMap R c (algebraMap R (CommonBase R c) (c 0:R)) at hyu
  rw [AlgHom.commutes] at hyu
  have huv := congrArg (commonMap R c).toRingHom (Units.mul_inv (reciprocalUnit R c))
  rw [map_mul,map_one] at huv
  have hd := D_reciprocal (R:=R) (S:=Overlap R c)
    (commonMap R c (rootUnit R c : CommonBase R c))
    (commonMap R c (reciprocalUnit R c : CommonBase R c))
    (commonMap R c (↑(reciprocalUnit R c)⁻¹ : CommonBase R c))
    (c 0 : R) hyu huv
  simpa only [derivativeFactor,map_neg,map_mul] using hd

/-- Normalize the fixed integer weight before entering the large native
cotangent tensor target. This lemma changes no scalar convention. -/
theorem map_weight {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    f ((VerticalSection318.J:A)^2)=(VerticalSection318.J:B)^2 := by
  simp only [map_pow,map_intCast]

/-- Whole-overlap agreement for the original J²-scaled first section. -/
theorem tensor0_agreement :
    (finiteMap R c ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
      IntegralBranchBicanonical318.coefficient0 R c 0)) •
        (finiteDifferential R c ⊗ₜ[Overlap R c] finiteDifferential R c) =
    (infinityMap R c ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
      IntegralInfinityCoefficients318.coefficient0 R c)) •
        (infinityDifferential R c ⊗ₜ[Overlap R c] infinityDifferential R c) := by
  have hJf : finiteMap R c ((VerticalSection318.J:IntegralBranchCoordinates318.B R c 0)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (finiteMap R c).toRingHom
  have hJi : infinityMap R c ((VerticalSection318.J:IntegralInfinityChart318.Order R c)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (infinityMap R c).toRingHom
  have hc : commonMap R c (finite0 R c) * (commonMap R c (derivativeFactor R c))^2=
      commonMap R c (infinity0 R c) := by
    have h := congrArg (commonMap R c).toRingHom (coefficient0_transition R c)
    simpa only [map_mul,map_pow] using h
  have ht := tensor_agreement (R:=R) (S:=Overlap R c)
    ((VerticalSection318.J:Overlap R c)^2) (commonMap R c (finite0 R c))
    (commonMap R c (infinity0 R c)) (commonMap R c (derivativeFactor R c))
    (finiteDifferential R c) (infinityDifferential R c) (differential_transition R c) hc
  simpa only [map_mul,hJf,hJi,finite_coefficient0,infinity_coefficient0] using ht

/-- The second original section agrees on the same entire overlap, with
its own finite and reciprocal coefficient formulas. -/
theorem tensor1_agreement :
    (finiteMap R c ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
      IntegralBranchBicanonical318.coefficient1 R c 0)) •
        (finiteDifferential R c ⊗ₜ[Overlap R c] finiteDifferential R c) =
    (infinityMap R c ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
      IntegralInfinityCoefficients318.coefficient1 R c)) •
        (infinityDifferential R c ⊗ₜ[Overlap R c] infinityDifferential R c) := by
  have hJf : finiteMap R c ((VerticalSection318.J:IntegralBranchCoordinates318.B R c 0)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (finiteMap R c).toRingHom
  have hJi : infinityMap R c ((VerticalSection318.J:IntegralInfinityChart318.Order R c)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (infinityMap R c).toRingHom
  have hc : commonMap R c (finite1 R c) * (commonMap R c (derivativeFactor R c))^2=
      commonMap R c (infinity1 R c) := by
    have h := congrArg (commonMap R c).toRingHom (coefficient1_transition R c)
    simpa only [map_mul,map_pow] using h
  have ht := tensor_agreement (R:=R) (S:=Overlap R c)
    ((VerticalSection318.J:Overlap R c)^2) (commonMap R c (finite1 R c))
    (commonMap R c (infinity1 R c)) (commonMap R c (derivativeFactor R c))
    (finiteDifferential R c) (infinityDifferential R c) (differential_transition R c) hc
  simpa only [map_mul,hJf,hJi,finite_coefficient1,infinity_coefficient1] using ht
end IntegralOverlapTensorCompatibility318
