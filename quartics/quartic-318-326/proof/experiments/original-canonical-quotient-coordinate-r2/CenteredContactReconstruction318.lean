module
public import CenteredDVRRestriction318
public import OriginalCurveActionComparison318
public section
noncomputable section
open scoped BigOperators
namespace CenteredContactReconstruction318
open Polynomial IsLocalRing LinearContactSquareclass318 IsDiscreteValuationRing
open AlgebraicGeometry CategoryTheory FourBinaryCharacters318
universe u
section Fields
variable {L : Type u} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- Actual local rings centered at original polynomial primes. Only the order
of that ONE prime is supplied, not a whole-field valuation restriction law. -/
structure LocalModel (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) where
  Ring : Type u
  [ring : CommRing Ring]
  [domain : IsDomain Ring]
  [dvr : IsDiscreteValuationRing Ring]
  [algebra : Algebra Ring L]
  [fraction : IsFractionRing Ring L]
  [residueCharZero : CharZero (ResidueField Ring)]
  coefficients : ℚ[X] →+* Ring
  coefficient_square : ∀ P, algebraMap Ring L (coefficients P) =
    algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) P)
  center : ∀ P, residue Ring (coefficients P) = 0 ↔ q ∣ P
  local_cases :
    (addVal Ring (coefficients q) = 1 ∧
      ∀ k, ¬ Associated q (X - C (contacts k))) ∨
    ∃ (k : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) (τ : Ring ≃+* Ring),
      Associated q (X - C (contacts k)) ∧ labels σ = flip k ∧
      addVal Ring (coefficients q) = 2 ∧
      (∀ x : Ring, σ (algebraMap Ring L x) = algebraMap Ring L (τ x)) ∧
      ∀ x : Ring, residue Ring (τ x) = residue Ring x

attribute [instance] LocalModel.ring LocalModel.domain LocalModel.dvr LocalModel.algebra
  LocalModel.fraction LocalModel.residueCharZero

/-- The original whole-field index1/2 laws are constructed from the actual
center maps, on precisely the SAME local ring and original fraction field. -/
@[expose] def toTame
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) (d : LocalModel labels q hq) :
    OriginalTangentFieldReconstruction318.LocalModel labels q hq where
  Ring := d.Ring
  local_cases := by
    rcases d.local_cases with hu | ⟨k, σ, τ, hc, hl, he, hs, hr⟩
    · refine Or.inl ⟨?_, hu.2⟩
      intro a ha
      simpa only [one_nsmul] using CenteredDVRRestriction318.restriction q hq d.coefficients
        d.coefficient_square d.center 1 hu.1 a ha
    · refine Or.inr ⟨k, σ, τ, hc, hl, ?_, hs, hr⟩
      exact CenteredDVRRestriction318.restriction q hq d.coefficients
        d.coefficient_square d.center 2 he

/-- End-to-end original function-field reconstruction, without a supplied
whole-field restriction, tangent sign, uniformizer, parity or field degree. -/
theorem field_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (signPattern (labels σ)) z) :=
  OriginalTangentFieldReconstruction318.reconstruct labels
    (fun q hq => toTame labels q hq (models q hq))

end Fields

section Curves
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme} [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

/-- Original curve identification through the already constructed SAME
normalization comparison, now consuming genuine centered local models. -/
theorem original_curve_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (signPattern (labels σ)) z) :=
  OriginalCandidateCurveIso318.exists_original_curve_iso g p hbase V hcover hnormal labels
    (fun q hq => toTame labels q hq (models q hq))
end Curves
end CenteredContactReconstruction318
