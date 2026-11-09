module
public import LocalBranchEquationOrders318
public import CenteredContactReconstruction318
public section
noncomputable section
namespace OriginalAffineLocalReconstruction318
open Polynomial IsLocalRing LinearContactSquareclass318
open AlgebraicGeometry CategoryTheory FourBinaryCharacters318
universe u
section Fields
variable {L : Type u} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- Genuine affine geometry on the original field. No local DVR, residue
characteristic, local automorphism, all-local residue action, canonical
valuation multiplier or whole-field restriction law is supplied. -/
structure Model (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) where
  Ring : Type u
  [ring : CommRing Ring]
  [domain : IsDomain Ring]
  [noetherian : IsNoetherianRing Ring]
  [normal : IsIntegrallyClosed Ring]
  [algebra : Algebra Ring L]
  [fraction : IsFractionRing Ring L]
  coefficients : ℚ[X] →+* Ring
  coefficient_square : ∀ a, algebraMap Ring L (coefficients a) =
    algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) a)
  prime : Ideal Ring
  [prime_prime : prime.IsPrime]
  height : prime.height = 1
  contraction : prime.comap coefficients = Ideal.span {q}
  local_cases :
    (maximalIdeal (Localization.AtPrime prime) =
        Ideal.span {AffinePrimeCenter318.coefficients prime coefficients q} ∧
      ∀ k, ¬ Associated q (X - C (contacts k))) ∨
    ∃ (k : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) (a : Ring ≃+* Ring)
        (π : Localization.AtPrime prime) (u : (Localization.AtPrime prime)ˣ),
      Associated q (X - C (contacts k)) ∧ labels σ = flip k ∧
      π ≠ 0 ∧ maximalIdeal (Localization.AtPrime prime) = Ideal.span {π} ∧
      AffinePrimeCenter318.coefficients prime coefficients q = (u : Localization.AtPrime prime) * π ^ 2 ∧
      prime = prime.comap a ∧
      (∀ b : Ring, σ (algebraMap Ring L b) = algebraMap Ring L (a b)) ∧
      ∀ b : Ring, a b - b ∈ prime

attribute [instance] Model.ring Model.domain Model.noetherian Model.normal
  Model.algebra Model.fraction Model.prime_prime

/-- Build the earlier centered model on the literal height-one localization
of the supplied original affine ring. All local maps are forced by that ring. -/
@[expose] def toCentered
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) (d : Model labels q hq) :
    CenteredContactReconstruction318.LocalModel labels q hq := by
  let R := Localization.AtPrime d.prime
  letI : IsDiscreteValuationRing R := HeightOneDVR318.localization d.prime d.height
  letI : Algebra R L := PrimeLocalOriginalField318.originalAlgebra d.Ring L d.prime
  letI : IsFractionRing R L := PrimeLocalOriginalField318.fraction d.Ring L d.prime
  letI : CharZero (ResidueField R) :=
    AffinePrimeCenter318.residue_charZero d.prime d.coefficients
  have hs : ∀ a, algebraMap R L (AffinePrimeCenter318.coefficients d.prime d.coefficients a) =
      algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) a) :=
    AffinePrimeCenter318.coefficient_square d.prime d.coefficients d.coefficient_square
  refine { Ring := R
           coefficients := AffinePrimeCenter318.coefficients d.prime d.coefficients
           coefficient_square := hs
           center := AffinePrimeCenter318.center d.prime d.coefficients q d.contraction
           local_cases := ?_ }
  rcases d.local_cases with hu | ⟨k, σ, a, π, u, hc, hl, hπ, hm, he, hP, hg, hr⟩
  · have hn : AffinePrimeCenter318.coefficients d.prime d.coefficients q ≠ 0 :=
      CenteredDVRRestriction318.coefficient_ne_zero
        (AffinePrimeCenter318.coefficients d.prime d.coefficients) hs q hq.ne_zero
    exact Or.inl ⟨LocalBranchEquationOrders318.unramified _ hn hu.1, hu.2⟩
  · refine Or.inr ⟨k, σ,
      PrimeLocalizationInertia318.lift d.prime R a hP, hc, hl,
      LocalBranchEquationOrders318.quadratic _ π hπ hm u he, ?_, ?_⟩
    · exact AffinePrimeOriginalInertia318.generic_square d.prime a hP σ.toRingEquiv hg
    · exact AffinePrimeOriginalInertia318.residue_identity d.prime a hP hr

/-- End-to-end reconstruction from actual affine local equations and original
prime-preserving affine inertia, without supplying abstract local models. -/
theorem field_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), Model labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (signPattern (labels σ)) z) :=
  CenteredContactReconstruction318.field_reconstruction labels
    (fun q hq => toCentered labels q hq (models q hq))
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

/-- The SAME original-candidate whole-curve isomorphism is constructed after
all actual affine local data have been joined. Genuine PEL existence and its
specific branch equations remain geometric obligations. -/
theorem original_curve_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), Model labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (signPattern (labels σ)) z) :=
  CenteredContactReconstruction318.original_curve_reconstruction g p hbase V hcover hnormal labels
    (fun q hq => toCentered labels q hq (models q hq))
end Curves
end OriginalAffineLocalReconstruction318
