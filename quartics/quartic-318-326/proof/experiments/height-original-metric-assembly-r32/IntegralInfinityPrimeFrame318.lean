module
public import IntegralInfinityHeightOne318
public section
noncomputable section
namespace IntegralInfinityPrimeFrame318
open IntegralInfinityChart318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] (c : Fin 4 → Rˣ)
  (P : Ideal (Order R c)) [P.IsPrime]
abbrev nativeCotangentModule (A T : Type*) [CommRing A] [CommRing T] [Algebra A T] :
    Module T (KaehlerDifferential A T) := inferInstance
local instance primeCotangentModule :
    Module (Localization.AtPrime P) (KaehlerDifferential R (Localization.AtPrime P)) :=
  nativeCotangentModule R (Localization.AtPrime P)

/-- At every original infinity-chart prime, including those containing u,
the actual reciprocal differential supplies the local frame. -/
@[expose] def localFrame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P :=
  LocalizedKaehlerFrame318.localFrame (T := Localization.AtPrime P) P.primeCompl (frame R c h2)

theorem localFrame_D (h2 : IsUnit (2 : R)) :
    localFrame R c P h2
      (KaehlerDifferential.D R (Localization.AtPrime P)
        (algebraMap (Order R c) (Localization.AtPrime P) (coordinate R c))) = 1 :=
  LocalizedKaehlerFrame318.localFrame_normalized (T := Localization.AtPrime P)
    P.primeCompl (frame R c h2) (coordinate R c) (frame_D R c h2)

/-- The same original local ring now has both the constructed DVR structure
and the constructed normalized differential frame. No u-nonzero condition. -/
theorem height_one_geometry [IsDomain R] [Algebra R ℚ]
    [IsIntegrallyClosed R] [IsNoetherianRing R]
    (hR : Function.Injective (algebraMap R ℚ)) (h2 : IsUnit (2 : R)) (hP : P.height=1) :
    letI := IntegralInfinityHeightOne318.localization_domain R c hR P
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      ∃ e : KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
        Localization.AtPrime P,
        e (KaehlerDifferential.D R (Localization.AtPrime P)
          (algebraMap (Order R c) (Localization.AtPrime P) (coordinate R c))) = 1 := by
  letI := IntegralInfinityHeightOne318.localization_domain R c hR P
  exact ⟨IntegralInfinityHeightOne318.localization_dvr R c hR h2 P hP,
    localFrame R c P h2,localFrame_D R c P h2⟩
end IntegralInfinityPrimeFrame318
