module
public import IntegralSourceBranches318
public import EtaleDifferentialFrame318
public import LocalizedKaehlerFrame318
public section
noncomputable section
namespace IntegralBranchFrames318
open IntegralSourceBranches318
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (i : Fin 4)

/-- The ramified root, not the original t parameter, supplies the integral frame. -/
@[expose] def rootFrame :
    KaehlerDifferential R (BranchBase R c i) ≃ₗ[BranchBase R c i] BranchBase R c i :=
  EtaleDifferentialFrame318.ofAlgEquiv
    (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).symm
    (KaehlerDifferential.polynomialEquiv R)

@[expose] def baseFrame :
    KaehlerDifferential R (OpenBase R c i) ≃ₗ[OpenBase R c i] OpenBase R c i :=
  LocalizedKaehlerFrame318.localFrame
    (Submonoid.powers (IntegralBranchChart318.denominator
      (c i) (contacts R i) (otherTwist R c i) (otherContact R i))) (rootFrame R c i)

/-- A genuine free cotangent module on the whole integral contact chart. -/
@[expose] def frame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (OpenOrder R c i) ≃ₗ[OpenOrder R c i] OpenOrder R c i := by
  letI : Algebra.Etale (OpenBase R c i) (OpenOrder R c i) :=
    (finite_free_etale R c h2 i).2.2
  exact LocalizedKaehlerFrame318.etaleFrame (baseFrame R c i)

-- Resolve the same native Kaehler module before specializing the nested
-- source order and prime localization; do not replace its scalar action.
abbrev nativeCotangentModule (A T : Type*) [CommRing A] [CommRing T]
    [Algebra A T] : Module T (KaehlerDifferential A T) := inferInstance
local instance primeCotangentModule (P : Ideal (OpenOrder R c i)) [P.IsPrime] :
    Module (Localization.AtPrime P) (KaehlerDifferential R (Localization.AtPrime P)) :=
  nativeCotangentModule R (Localization.AtPrime P)

/-- This is the actual frame at each prime of the integral contact chart. -/
@[expose] def atPrimeFrame (h2 : IsUnit (2 : R))
    (P : Ideal (OpenOrder R c i)) [P.IsPrime] :
    KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P :=
  LocalizedKaehlerFrame318.localFrame (T := Localization.AtPrime P) P.primeCompl (frame R c i h2)

end IntegralBranchFrames318
