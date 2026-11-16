module
public import IntegralInfinityCotangentFiber318
public section
noncomputable section
namespace IntegralOverlapCotangentParameter318
open IntegralOverlapChartMaps318 IntegralOverlapTensorCompatibility318
open IntegralOverlapCoefficientRestrictions318 IntegralOverlapCoefficients318
open IntegralInfinityCommonBase318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance overlapCotangentModule : Module (Overlap R c) (KaehlerDifferential R (Overlap R c)) :=
  nativeCotangentModule R (Overlap R c)
@[expose] def factor : Overlap R c :=
  (finiteMap R c (2*algebraMap R (IntegralBranchCoordinates318.B R c 0) (↑(c 0)⁻¹:R)*
    IntegralBranchCoordinates318.sourceCoordinate R c 0))*commonMap R c (derivativeFactor R c)

/-- The original Dt is identified in the ACTUAL common Kähler module,
using the genuine finite and infinity restriction maps and the signed
reciprocal Jacobian. No rational-point equality is used to infer this. -/
theorem differential_parameter :
    KaehlerDifferential.D R (Overlap R c)
      (finiteMap R c (IntegralBranchCoordinates318.sourceT R c 0))=
        factor R c • infinityDifferential R c := by
  have h := congrArg (AlgHomDifferential318.map (finiteMap R c))
    (SquareCoordinateDifferential318.D_of_square
      (IntegralBranchCoordinates318.sourceT R c 0)
      (IntegralBranchCoordinates318.sourceCoordinate R c 0)
      (IntegralSourceBranches318.contacts R 0) (↑(c 0)⁻¹:R)
      (IntegralBranchCoordinates318.coordinate_square R c 0))
  simp only [AlgHomDifferential318.map_D,AlgHomDifferential318.map_smul] at h
  change _= (finiteMap R c (2*algebraMap R (IntegralBranchCoordinates318.B R c 0)
    (↑(c 0)⁻¹:R)*IntegralBranchCoordinates318.sourceCoordinate R c 0)) • finiteDifferential R c at h
  rw [h,differential_transition,smul_smul]
  all_goals rfl

variable (K : Type*) [Field K] (ρ : Overlap R c →+* K)
@[expose] def finiteEvaluation := ρ.comp (finiteMap R c).toRingHom
@[expose] def infinityEvaluation := ρ.comp (infinityMap R c).toRingHom
@[expose] def derivative : K := ρ (factor R c)

theorem jacobian_unit : IsUnit (commonMap R c (derivativeFactor R c)) := by
  have hu : IsUnit (derivativeFactor R c) :=
    ((rootUnit R c).isUnit.mul ((reciprocalUnit R c)⁻¹).isUnit).neg
  exact hu.map (commonMap R c)

/-- The exact coefficient identity is transported through the actual common
point, including J², the original denominator and signed Jacobian. -/
theorem coefficient_transition (n : Fin 2) :
    infinityEvaluation R c K ρ (IntegralGlobalBicanonicalPair318.infinityCoefficient R c n)=
      finiteEvaluation R c K ρ (IntegralGlobalBicanonicalPair318.branchCoefficient R c 0 n)*
        ρ (commonMap R c (derivativeFactor R c))^2 := by
  have h0 := congrArg (fun a : CommonBase R c => ρ (commonMap R c a)) (coefficient0_transition R c)
  have h1 := congrArg (fun a : CommonBase R c => ρ (commonMap R c a)) (coefficient1_transition R c)
  fin_cases n
  · simp only [IntegralGlobalBicanonicalPair318.infinityCoefficient,
      IntegralGlobalBicanonicalPair318.branchCoefficient,if_pos rfl,
      infinityEvaluation,finiteEvaluation,RingHom.comp_apply,map_mul,map_pow,map_intCast,
      infinity_coefficient0,finite_coefficient0] at *
    simp only [map_mul,map_pow] at h0
    rw [←h0]
    ring
  · simp only [IntegralGlobalBicanonicalPair318.infinityCoefficient,
      IntegralGlobalBicanonicalPair318.branchCoefficient,show (1:Fin 2)≠0 by decide,ite_false,
      infinityEvaluation,finiteEvaluation,RingHom.comp_apply,map_mul,map_pow,map_intCast,
      infinity_coefficient1,finite_coefficient1] at *
    simp only [map_mul,map_pow] at h1
    rw [←h1]
    ring

variable (h2 : IsUnit (2:R))
include h2 in
theorem derivative_ne (hP : finiteEvaluation R c K ρ
    (IntegralBranchBicanonical318.sourceP R c 0)≠0) : derivative R c K ρ≠0 := by
  have hd := IntegralBranchCotangentFiber318.dt_ne R c 0 h2 K (finiteEvaluation R c K ρ) hP
  rw [IntegralBranchCotangentFiber318.dt_value] at hd
  unfold derivative factor
  rw [map_mul]
  exact mul_ne_zero hd (((jacobian_unit R c).map ρ).ne_zero)

include h2 in
/-- Cleared J²/DT normalization on the actual infinity chart, obtained from
the whole-overlap differential and coefficient identities. -/
theorem cleared_section :
    finiteEvaluation R c K ρ (IntegralBranchBicanonical318.sourceP R c 0)*
      infinityEvaluation R c K ρ (IntegralGlobalBicanonicalPair318.infinityCoefficient R c 0)=
        (VerticalSection318.J:K)^2*(derivative R c K ρ)^2 := by
  have h := IntegralBranchCotangentFiber318.cleared_section R c 0 h2 K (finiteEvaluation R c K ρ)
  rw [IntegralBranchCotangentFiber318.dt_value] at h
  rw [coefficient_transition]
  change _=(VerticalSection318.J:K)^2*(ρ (factor R c))^2
  rw [factor,map_mul]
  change _=(VerticalSection318.J:K)^2*
    (finiteEvaluation R c K ρ _ * ρ (commonMap R c (derivativeFactor R c)))^2
  calc
    _ = (finiteEvaluation R c K ρ (IntegralBranchBicanonical318.sourceP R c 0)*
      finiteEvaluation R c K ρ (IntegralGlobalBicanonicalPair318.branchCoefficient R c 0 0))*
        ρ (commonMap R c (derivativeFactor R c))^2 := by ring
    _ = _ := by rw [h]; ring
end IntegralOverlapCotangentParameter318
