module
public import IntegralNormalTraceSheafDuality318
public import OriginalNormalizationPushforward318
public section
noncomputable section
namespace OriginalNormalAffineDuality318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "π" => AffineFiniteDualSheafAdjunction318.projection P N

/-- The projection used in the duality is the literal polynomial-base
projection of the actual affine normal chart, not an auxiliary finite map. -/
theorem finite_projection : IsFinite π := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  letI : Module.Finite (IntegralDistinctContactOpen318.Base R a d) B :=
    (IntegralDistinctContactOpen318.finite_free_etale R a d).1
  letI : Algebra.Etale (IntegralDistinctContactOpen318.Base R a d) B :=
    (IntegralDistinctContactOpen318.finite_free_etale R a d).2.2
  let s := IntegralNormalizationConductorDenominator318.denominator R a d
  have hs : s ≠ 0 := IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
    (IntegralDistinctContactOpen318.arithmeticDenominator_ne_zero R d
      (coefficients_ne_zero c t w D))
  letI : Module.Finite P N := (LocalizedNormalModel318.finite_normal_model
    (Rf:=IntegralDistinctContactOpen318.Base R a d) (B:=B) s hs).1
  exact IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- This is the SAME structural morphism into the SAME original proper
normal model, with the exact original affine base chart. -/
theorem original_projection_square :
    OriginalNormalOrderChart318.chart c t w D M ≫ M.projection=
      π ≫ JLineAtlas318.chart R 1 :=
  OriginalNormalOrderChart318.base c t w D M

@[expose] def homEquiv (Q : ModuleCat N) :
    (tilde Q ⟶ IntegralNormalTraceSheafDuality318.traceSheaf R a d) ≃
      ((Scheme.Modules.pushforward π).obj (tilde Q) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P P)) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalTraceSheafDuality318.homEquiv R a d (coefficients_ne_zero c t w D) Q

/-- Every actual base-sheaf functional on every native affine module
pushforward has its unique actual trace-dual sheaf lift on this chart. -/
theorem existsUnique_lift (Q : ModuleCat N)
    (g : (Scheme.Modules.pushforward π).obj (tilde Q) ⟶
      tilde (R:=CommRingCat.of P) (ModuleCat.of P P)) :
    ∃! f : tilde Q ⟶ IntegralNormalTraceSheafDuality318.traceSheaf R a d,
      homEquiv c t w D Q f=g := by
  refine ⟨(homEquiv c t w D Q).symm g,(homEquiv c t w D Q).apply_symm_apply g,?_⟩
  intro f hf
  apply (homEquiv c t w D Q).injective
  exact hf.trans ((homEquiv c t w D Q).apply_symm_apply g).symm
end OriginalNormalAffineDuality318
