module
public import IntegralDistinctContactOpen318
public import ActualEtaleFrameNormalization318
public import QuadraticCotangentFrameRelation318
public import FourRootOrderSigns318
public section
noncomputable section
namespace IntegralNormalSourceDifferentialFrame318
open Polynomial KaehlerDifferential IntegralDistinctContactOpen318
set_option maxHeartbeats 800000
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)

/-- The base is the actual arithmetic localization used in the same
normal-model source, including its original denominator. -/
@[expose] def baseFrame : KaehlerDifferential R (Base R a d) ≃ₗ[Base R a d] Base R a d := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := Base R a d)
    (Submonoid.powers (IntegralReciprocalBase318.finiteDenominator R a
      (arithmeticDenominator R d)))
  exact EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv R)

/-- A constructed dt frame on the SAME open order inside the proper
normal model. This is not a smoothness claim on its excluded special fiber. -/
@[expose] def frame : KaehlerDifferential R (OpenOrder R a d) ≃ₗ[OpenOrder R a d]
    OpenOrder R a d := by
  letI : Algebra.Etale (Base R a d) (OpenOrder R a d) := (finite_free_etale R a d).2.2
  exact EtaleDifferentialFrame318.ofFormallyEtale (baseFrame R a d)

@[expose] def coordinate : OpenOrder R a d :=
  algebraMap (Base R a d) (OpenOrder R a d) (algebraMap R[X] (Base R a d) X)

/-- The normalization is exact, not a rank-only assertion or an arbitrary
unit multiple of the differential of the original t-coordinate. -/
theorem frame_D : frame R a d (D R (OpenOrder R a d) (coordinate R a d)) = 1 := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := Base R a d)
    (Submonoid.powers (IntegralReciprocalBase318.finiteDenominator R a
      (arithmeticDenominator R d)))
  letI : Algebra.Etale (Base R a d) (OpenOrder R a d) := (finite_free_etale R a d).2.2
  change EtaleDifferentialFrame318.ofFormallyEtale (baseFrame R a d)
    (D R _ (algebraMap _ _ _)) = 1
  rw [ActualEtaleFrameNormalization318.ofFormallyEtale_D]
  change algebraMap (Base R a d) (OpenOrder R a d)
    (EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv R)
      (D R (Base R a d) (algebraMap R[X] (Base R a d) X))) = 1
  rw [ActualEtaleFrameNormalization318.ofFormallyEtale_D,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one,map_one]

@[expose] def root (i : Fin 4) : OpenOrder R a d :=
  FourRootOrderSigns318.generator
    (fun j => algebraMap R[X] (Base R a d)
      (DistinctContactIntegralDomain318.coefficient R a d j)) i

theorem root_square (i : Fin 4) : (root R a d i)^2 =
    algebraMap R (OpenOrder R a d) (d i) *
      (coordinate R a d - algebraMap R (OpenOrder R a d) (a i)) := by
  rw [root,FourRootOrderSigns318.generator_square]
  simp only [DistinctContactIntegralDomain318.coefficient,map_mul,map_sub,
    IntegralReciprocalBase318.finite_C,
    ←IsScalarTower.algebraMap_apply R (Base R a d) (OpenOrder R a d)]
  rfl

/-- The actual original normalized root, with its sign still fixed,
obeys the differentiated quadratic equation in this exact source frame. -/
theorem root_differential (i : Fin 4) :
    2 * root R a d i * frame R a d (D R (OpenOrder R a d) (root R a d i)) =
      algebraMap R (OpenOrder R a d) (d i) :=
  QuadraticCotangentFrameRelation318.relation (frame R a d)
    (coordinate R a d) (root R a d i) (a i) (d i) (frame_D R a d) (root_square R a d i)
end IntegralNormalSourceDifferentialFrame318
