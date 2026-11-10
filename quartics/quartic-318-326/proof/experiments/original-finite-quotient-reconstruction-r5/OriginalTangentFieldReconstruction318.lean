module
public import TameInvolutionUniformizer318
public import LabeledContactInertiaSigns318
public section
noncomputable section
open scoped BigOperators
namespace OriginalTangentFieldReconstruction318
open Polynomial IsLocalRing LinearContactSquareclass318
open DVRFractionCharacterParity318 PolynomialPrimeValuation318
open GaloisCharacterContactReconstruction318 FourBinaryCharacters318
universe u
variable {L : Type u} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- Original local geometry in terms of labeled branch prime, actual local
inertia and its full residue action. No uniformizer, tangent congruence or
four character equations are supplied: all are constructed on the SAME ring. -/
structure LocalModel (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) where
  Ring : Type u
  [ring : CommRing Ring]
  [domain : IsDomain Ring]
  [dvr : IsDiscreteValuationRing Ring]
  [algebra : Algebra Ring L]
  [fraction : IsFractionRing Ring L]
  [residueCharZero : CharZero (ResidueField Ring)]
  local_cases :
    ((∀ a : RatFunc ℚ, a ≠ 0 →
        value Ring L (algebraMap (RatFunc ℚ) L a) = primePlace q hq a) ∧
      ∀ k, ¬ Associated q (X - C (contacts k))) ∨
    ∃ (k : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) (τ : Ring ≃+* Ring),
      Associated q (X - C (contacts k)) ∧ labels σ = flip k ∧
      (∀ a : RatFunc ℚ, a ≠ 0 →
        value Ring L (algebraMap (RatFunc ℚ) L a) = 2 • primePlace q hq a) ∧
      (∀ x : Ring, σ (algebraMap Ring L x) = algebraMap Ring L (τ x)) ∧
      ∀ x : Ring, residue Ring (τ x) = residue Ring x

attribute [instance] LocalModel.ring LocalModel.domain LocalModel.dvr LocalModel.algebra
  LocalModel.fraction LocalModel.residueCharZero

/-- A construction on the SAME actual local ring and fraction field. -/
@[expose] def toInertia
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) (d : LocalModel labels q hq) :
    OriginalInertiaFieldReconstruction318.LocalModel labels q hq where
  Ring := d.Ring
  local_cases := by
    rcases d.local_cases with hu | ⟨k, σ, τ, hqk, hlabel, hr, hc, hres⟩
    · exact Or.inl ⟨hu.1, LabeledContactInertiaSigns318.outside_cubics q hq hu.2⟩
    · have hτ : ∀ x, τ (τ x) = x := by
        intro x
        apply IsFractionRing.injective d.Ring L
        rw [← hc, ← hc, LabeledContactInertiaSigns318.original_involution labels]
      have hmoves : ∃ x : d.Ring, τ x ≠ x := by
        by_contra h
        have hfix : ∀ x : d.Ring, τ x = x := by
          simpa only [not_exists, not_not] using h
        have hσ : σ = 1 := by
          ext z
          obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective d.Ring z
          change σ (algebraMap d.Ring L a / algebraMap d.Ring L b) =
            algebraMap d.Ring L a / algebraMap d.Ring L b
          simp only [map_div₀, hc, hfix]
        have hflip : flip k = 1 := by rw [← hlabel, hσ, map_one]
        exact LabeledContactInertiaSigns318.flip_ne_one k hflip
      obtain ⟨π, hanti, hneg⟩ :=
        TameInvolutionUniformizer318.exists_anti_uniformizer τ hτ hres hmoves
      exact Or.inr ⟨σ, τ, π, hr, hc, hres, hanti,
        hneg, LabeledContactInertiaSigns318.original_sign labels σ k hlabel q hqk⟩

/-- The end-to-end field isomorphism preserves the original labeled action.
Actual PEL field, branch coordinates, local rings, actual inertia/residue
actions and full index1/2 restrictions remain geometric prerequisites. The
tangent sign and eigen-uniformizer are now derived, not supplied. -/
theorem reconstruct
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (signPattern (labels σ)) z) :=
  OriginalInertiaFieldReconstruction318.reconstruct labels
    (fun q hq => toInertia labels q hq (models q hq))
end OriginalTangentFieldReconstruction318
