module
public import FourRootWholeCanonicalCover318
public import ActualIntrinsicMeromorphicSections318
public import FourRootActualBaseDifferentialOrders318
public section
noncomputable section
namespace FourRootCanonicalMeromorphicBridge318
open AlgebraicGeometry CategoryTheory
open FourRootIntrinsicCanonicalFrames318 FourRootGluedScheme318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev A:=FourRootAffineCoordinateRing318.Ring b
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
@[expose] def finiteRealization(i:Fin 4):
    Γ(omega b,finiteEmbedding b i ''ᵁ ⊤)→+KaehlerDifferential ℂ (FractionRing (A b)):=
  ActualIntrinsicMeromorphicSections318.realization (A b)
    (FourRootActualFiniteBranchChart318.denominator b i)
    (FourRootActualMeromorphicFinite318.denominator_ne b hb i)
    (finiteEmbedding b i) (structureMap b) (finite_structure b i)
@[expose] def infinityRealization:
    Γ(omega b,infinityEmbedding b hb ''ᵁ ⊤)→+KaehlerDifferential ℂ (FractionRing (I b)):=
  ActualIntrinsicMeromorphicSections318.realization (I b)
    (FourRootActualInfinityKaehler318.denominator b hb)
    (FourRootActualMeromorphicInfinity318.denominator_ne b hb)
    (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
/-- The original dt whose signed orders were computed is the actual
meromorphic realization of the intrinsic global Omega derivative of
the original projective coordinate, on EVERY finite canonical chart. -/
theorem original_dt_realized(i:Fin 4):
    finiteRealization b hb i
      ((FamilyIntrinsicDifferentials318.D (structureMap b)).d
        (((finiteEmbedding b i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
            (FourRootActualBranchKaehler318.sourceParameter b i))))=
    KaehlerDifferential.D ℂ (FractionRing (A b)) (FourRootActualMeromorphicFinite318.t b):=by
  rw [finiteRealization,ActualIntrinsicMeromorphicSections318.realization_derivative]
  congr 1
  exact ActualLocalizationDifferentialFrame318.on_source (A b)
    (FourRootActualFiniteBranchChart318.denominator b i)
    (FourRootActualMeromorphicFinite318.denominator_ne b hb i) _
/-- The infinity frame used to compute the ORIGINAL dt pole is exactly
the actual canonical sheaf generator du after genuine realization. -/
theorem original_du_realized:
    infinityRealization b hb (infinityGenerator b hb)=
      KaehlerDifferential.D ℂ (FractionRing (I b)) (FourRootActualMeromorphicInfinity318.u b):=by
  rw [infinityRealization,infinityGenerator,
    ActualIntrinsicMeromorphicSections318.realization_section,AlgHomDifferential318.map_D]
  congr 1
  exact ActualLocalizationDifferentialFrame318.on_source (I b)
    (FourRootActualInfinityKaehler318.denominator b hb)
    (FourRootActualMeromorphicInfinity318.denominator_ne b hb) _
/-- Same intrinsic canonical generator and same original function field;
no reciprocal dv is substituted for the meromorphic differential dt. -/
theorem original_dt_in_infinity_generator:
    KaehlerDifferential.D ℂ (FractionRing (I b)) (FourRootActualMeromorphicInfinity318.t b hb)=
    (-(2:FractionRing (I b))*(FourRootActualMeromorphicInfinity318.u b)⁻¹^3) •
      infinityRealization b hb (infinityGenerator b hb):=by
  apply (FourRootActualMeromorphicInfinity318.frame b hb).injective
  rw [FourRootActualMeromorphicInfinity318.dt_coefficient,map_smul,original_du_realized,
    FourRootActualMeromorphicInfinity318.du_coefficient,smul_eq_mul,mul_one]
end FourRootCanonicalMeromorphicBridge318
