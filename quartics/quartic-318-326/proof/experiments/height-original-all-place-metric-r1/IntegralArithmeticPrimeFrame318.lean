module
public import IntegralArithmeticHeightOne318
public import IntegralOriginalRootCoordinates318
public section
noncomputable section
namespace IntegralArithmeticPrimeFrame318
open IntegralSourceBranches318 IntegralBranchCoordinates318 IntegralBranchLocalization318
open IntegralOriginalRootCoordinates318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] (c : Fin 4 → Rˣ)
  (P : Ideal (SourceOrder R c)) [P.IsPrime]

/-- Every actual prime lies in an original complete branch chart on the
specified good arithmetic base; this is not restricted to generic points. -/
theorem prime_chart
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R)) :
    ∃ i : Fin 4, IntegralBranchDenominatorCover318.denominator R c i ∉ P := by
  by_contra! h
  have he : Ideal.span (Set.range (IntegralBranchDenominatorCover318.denominator R c)) ≤ P :=
    Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
  rw [IntegralBranchDenominatorCover318.span_top R c hN] at he
  exact (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)) (top_le_iff.mp he)

variable (i : Fin 4) (hi : IntegralBranchDenominatorCover318.denominator R c i ∉ P)
@[expose] def branchPrimeAlgebra : Algebra (B R c i) (Localization.AtPrime P) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (B R c i) (Localization.AtPrime P)
    (Submonoid.powers (IntegralBranchDenominatorCover318.denominator R c i)) P.primeCompl
    (Submonoid.powers_le.mpr hi)
local instance branchPrimeAlgebraInst : Algebra (B R c i) (Localization.AtPrime P) :=
  branchPrimeAlgebra R c P i hi
local instance sourceBranchPrimeTower :
    IsScalarTower (SourceOrder R c) (B R c i) (Localization.AtPrime P) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le (B R c i) (Localization.AtPrime P)
    (Submonoid.powers (IntegralBranchDenominatorCover318.denominator R c i)) P.primeCompl
    (Submonoid.powers_le.mpr hi)
local instance branchPrimeLocalization :
    IsLocalization (P.primeCompl.map (algebraMap (SourceOrder R c) (B R c i)))
      (Localization.AtPrime P) :=
  IsLocalization.isLocalization_of_submonoid_le (B R c i) (Localization.AtPrime P)
    (Submonoid.powers (IntegralBranchDenominatorCover318.denominator R c i)) P.primeCompl
    (Submonoid.powers_le.mpr hi)
local instance relativeBranchPrimeTower : IsScalarTower R (B R c i) (Localization.AtPrime P) :=
  IsScalarTower.of_algebraMap_eq (by
    intro r
    rw [IsScalarTower.algebraMap_apply R (SourceOrder R c) (B R c i),
      ←IsScalarTower.algebraMap_apply (SourceOrder R c) (B R c i) (Localization.AtPrime P),
      ←IsScalarTower.algebraMap_apply R (SourceOrder R c) (Localization.AtPrime P)])

abbrev nativeCotangentModule (A T : Type*) [CommRing A] [CommRing T] [Algebra A T] :
    Module T (KaehlerDifferential A T) := inferInstance
local instance primeCotangentModule :
    Module (Localization.AtPrime P) (KaehlerDifferential R (Localization.AtPrime P)) :=
  nativeCotangentModule R (Localization.AtPrime P)

/-- The actual relative cotangent frame on the original source prime ring,
constructed by further localization of the original signed branch frame. -/
@[expose] def frame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P :=
  LocalizedKaehlerFrame318.localFrame (T := Localization.AtPrime P)
    (P.primeCompl.map (algebraMap (SourceOrder R c) (B R c i))) (sourceFrame R c i h2)

theorem root_image :
    algebraMap (B R c i) (Localization.AtPrime P) (sourceCoordinate R c i) =
      algebraMap (SourceOrder R c) (Localization.AtPrime P) (root R c i) := by
  rw [coordinate_eq_root,←IsScalarTower.algebraMap_apply]

theorem frame_D_original_root (h2 : IsUnit (2 : R)) :
    frame R c P i hi h2
      (KaehlerDifferential.D R (Localization.AtPrime P)
        (algebraMap (SourceOrder R c) (Localization.AtPrime P) (root R c i))) = 1 := by
  rw [←root_image R c P i hi]
  exact LocalizedKaehlerFrame318.localFrame_normalized
    (T := Localization.AtPrime P)
    (P.primeCompl.map (algebraMap (SourceOrder R c) (B R c i)))
    (sourceFrame R c i h2) (sourceCoordinate R c i) (source_normalized R c i h2)

/-- The index and frame are actually produced at every source prime. No
local frame or choice of a different local ring remains a caller input. -/
theorem every_prime_frame (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R)) :
    ∃ i : Fin 4, ∃ e : KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P,
      e (KaehlerDifferential.D R (Localization.AtPrime P)
        (algebraMap (SourceOrder R c) (Localization.AtPrime P) (root R c i))) = 1 := by
  obtain ⟨j,hj⟩ := prime_chart R c P hN
  exact ⟨j,frame R c P j hj h2,frame_D_original_root R c P j hj h2⟩

/-- Connected actual geometry at every height-one prime: the original
local ring is a DVR and its relative differential module has a constructed
frame normalized at one of the original signed roots. -/
theorem height_one_geometry [IsDomain R] [Algebra R ℚ]
    [IsIntegrallyClosed R] [IsNoetherianRing R]
    (hR : Function.Injective (algebraMap R ℚ)) (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R))
    (hP : P.height=1) :
    letI := IntegralArithmeticHeightOne318.localization_domain R c hR P
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      ∃ j : Fin 4, ∃ e : KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
        Localization.AtPrime P,
        e (KaehlerDifferential.D R (Localization.AtPrime P)
          (algebraMap (SourceOrder R c) (Localization.AtPrime P) (root R c j))) = 1 := by
  letI := IntegralArithmeticHeightOne318.localization_domain R c hR P
  exact ⟨IntegralArithmeticHeightOne318.localization_dvr R c hR h2 hN P hP,
    every_prime_frame R c P h2 hN⟩
end IntegralArithmeticPrimeFrame318
