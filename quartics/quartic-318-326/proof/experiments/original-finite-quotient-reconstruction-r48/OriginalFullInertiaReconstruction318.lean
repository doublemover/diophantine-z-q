module
public import LabeledFullInertiaCardinality318
public import OriginalAffineLocalReconstruction318
public section
noncomputable section
namespace OriginalFullInertiaReconstruction318
open Polynomial IsLocalRing LinearContactSquareclass318
open AlgebraicGeometry CategoryTheory FourBinaryCharacters318
open OriginalNormalClosureGalois318
universe u
section Fields
variable {L : Type u} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- The remaining geometric branch input is the FULL ideal inertia of the
literal normal closure in the original field. Local rings, branch equations,
canonical orders, affine actions and residue characteristic are NOT inputs. -/
structure BranchAt (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) where
  prime : Ideal (Order L)
  [prime_prime : prime.IsPrime]
  contraction : prime.under ℚ[X] = Ideal.span {q}
  inertia_cases :
    ((∀ σ : OriginalNormalClosureGalois318.Group L, σ ∈ prime.inertia (OriginalNormalClosureGalois318.Group L) ↔ σ = 1) ∧
      ∀ k, ¬ Associated q (X - C (contacts k))) ∨
    ∃ k : Fin 4, Associated q (X - C (contacts k)) ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, σ ∈ prime.inertia (OriginalNormalClosureGalois318.Group L) ↔
        σ = 1 ∨ labels σ = flip k
attribute [instance] BranchAt.prime_prime

/-- A geometric branch-locus statement on EVERY original normal prime.
The construction below chooses no primes or local models as user inputs. -/
@[expose] def BranchLocus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group) : Prop :=
  ∀ (q : ℚ[X]), Prime q → ∀ P : Ideal (Order L), P.IsPrime →
    P.under ℚ[X] = Ideal.span {q} →
      ((∀ σ : OriginalNormalClosureGalois318.Group L, σ ∈ P.inertia (OriginalNormalClosureGalois318.Group L) ↔ σ = 1) ∧
        ∀ k, ¬ Associated q (X - C (contacts k))) ∨
      ∃ k : Fin 4, Associated q (X - C (contacts k)) ∧
        ∀ σ : OriginalNormalClosureGalois318.Group L, σ ∈ P.inertia (OriginalNormalClosureGalois318.Group L) ↔ σ = 1 ∨ labels σ = flip k

/-- Actual lying-over in the literal finite integral closure supplies the
required prime. Its contraction and full inertia are then joined exactly. -/
@[expose] def chooseBranch
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : BranchLocus labels) (q : ℚ[X]) (hq : Prime q) : BranchAt labels q hq := by
  letI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  let chosen : (Ideal.span {q}).primesOver (Order L) :=
    Classical.choice (Ideal.nonempty_primesOver (Ideal.span {q}))
  obtain ⟨P,hP,hO⟩ := chosen
  letI := hP
  letI := hO
  have hc : P.under ℚ[X] = Ideal.span {q} := (Ideal.over_def P (Ideal.span {q})).symm
  exact { prime := P, contraction := hc, inertia_cases := h q hq P hP hc }

/-- Isolate the exact original coefficient injection from local model assembly. -/
lemma original_coefficient_ne_zero (q : ℚ[X]) (hq : Prime q) :
    algebraMap ℚ[X] (Order L) q ≠ 0 := by
  intro hz
  have hh := congrArg (algebraMap (Order L) L) hz
  rw [coefficient_square,map_zero] at hh
  have hn := (algebraMap (RatFunc ℚ) L).injective.ne
    ((IsFractionRing.injective ℚ[X] (RatFunc ℚ)).ne hq.ne_zero)
  exact hn (by simpa only [map_zero] using hh)

lemma branch_prime_ne_bot
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) (d : BranchAt labels q hq) : d.prime ≠ ⊥ := by
  intro he
  have hm : algebraMap ℚ[X] (Order L) q ∈ d.prime := by
    change q ∈ d.prime.under ℚ[X]
    rw [d.contraction]
    exact Ideal.subset_span (by simp)
  rw [he,Ideal.mem_bot] at hm
  exact original_coefficient_ne_zero q hq hm

lemma localized_coefficient_square (P : Ideal (Order L)) [P.IsPrime] :
    letI := PrimeLocalOriginalField318.originalAlgebra (Order L) L P
    ∀ a : ℚ[X], algebraMap (Localization.AtPrime P) L
      (algebraMap ℚ[X] (Localization.AtPrime P) a) =
      algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) a) := by
  letI := PrimeLocalOriginalField318.originalAlgebra (Order L) L P
  intro a
  have hh := AffinePrimeCenter318.coefficient_square P
    (algebraMap ℚ[X] (Order L)) (coefficient_square L) a
  change PrimeLocalOriginalField318.embedding (Order L) L P
    (algebraMap ℚ[X] (Localization.AtPrime P) a) = _
  have hc : AffinePrimeCenter318.coefficients P (algebraMap ℚ[X] (Order L)) a =
      algebraMap ℚ[X] (Localization.AtPrime P) a :=
    (IsScalarTower.algebraMap_apply ℚ[X] (Order L) (Localization.AtPrime P) a).symm
  simpa only [hc] using hh

/-- Every required local input is constructed on the canonical localization
of the actual integral closure. The full inertia/cardinality theorem, with
its genuine hypotheses, replaces a supplied local ramification equation. -/
@[expose] def toCentered
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) (d : BranchAt labels q hq) :
    CenteredContactReconstruction318.LocalModel labels q hq := by
  let B := Order L
  let R := Localization.AtPrime d.prime
  have hP := branch_prime_ne_bot labels q hq d
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP R
  letI : Algebra R L := PrimeLocalOriginalField318.originalAlgebra B L d.prime
  letI : IsFractionRing R L := PrimeLocalOriginalField318.fraction B L d.prime
  letI : CharZero (ResidueField R) :=
    AffinePrimeCenter318.residue_charZero d.prime (algebraMap ℚ[X] B)
  have hc (a : ℚ[X]) : AffinePrimeCenter318.coefficients d.prime (algebraMap ℚ[X] B) a =
      algebraMap ℚ[X] R a :=
    (IsScalarTower.algebraMap_apply ℚ[X] B R a).symm
  have hs := localized_coefficient_square d.prime
  have hn : algebraMap ℚ[X] R q ≠ 0 :=
    CenteredDVRRestriction318.coefficient_ne_zero (F := ℚ) (R := R) (L := L)
      (algebraMap ℚ[X] R) hs q hq.ne_zero
  letI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  letI : Algebra.HasSeparableResidueFieldsAt ℚ[X] B (Ideal.span {q}) :=
    residue_separable L (Ideal.span {q})
  have horder := OriginalPrimeOrderInertia318.order_eq_inertia_card
    (G := OriginalNormalClosureGalois318.Group L) d.prime q d.contraction hn
  refine { Ring := R
           coefficients := algebraMap ℚ[X] R
           coefficient_square := hs
           center := ?_
           local_cases := ?_ }
  · intro a
    have hh := AffinePrimeCenter318.center d.prime (algebraMap ℚ[X] B) q d.contraction a
    simpa only [hc] using hh
  · rcases d.inertia_cases with hu | ⟨k,hk,hi⟩
    · have hcard := LabeledFullInertiaCardinality318.trivial_card
        (d.prime.inertia (OriginalNormalClosureGalois318.Group L)) hu.1
      exact Or.inl ⟨horder.trans (congrArg (fun n : ℕ => (n : ENat)) hcard),hu.2⟩
    · let σ : OriginalNormalClosureGalois318.Group L := labels.symm (flip k)
      have hl : labels σ = flip k := labels.apply_symm_apply _
      have hm : σ ∈ d.prime.inertia (OriginalNormalClosureGalois318.Group L) := (hi σ).mpr (Or.inr hl)
      let a := affineAction L σ
      have hr : ∀ b : B, a b - b ∈ d.prime := by
        intro b
        exact (Ideal.mem_inertia.mp hm) b
      have hp : d.prime = d.prime.comap a := by
        ext b
        change b ∈ d.prime ↔ a b ∈ d.prime
        constructor
        · intro hb
          simpa only [sub_add_cancel] using d.prime.add_mem (hr b) hb
        · intro hb
          simpa only [sub_sub_cancel] using d.prime.sub_mem hb (hr b)
      have hcard := LabeledFullInertiaCardinality318.labeled_card labels
        (d.prime.inertia (OriginalNormalClosureGalois318.Group L)) k hi
      refine Or.inr ⟨k,σ,PrimeLocalizationInertia318.lift d.prime R a hp,hk,hl,
        horder.trans (congrArg (fun n : ℕ => (n : ENat)) hcard),?_,?_⟩
      · exact AffinePrimeOriginalInertia318.generic_square d.prime a hp σ.toRingEquiv
          (affineAction_generic L σ)
      · exact AffinePrimeOriginalInertia318.residue_identity d.prime a hp hr

/-- Reconstruct the SAME original field from its full labeled geometric
inertia, with all canonical normal-ring and ramification algebra internal. -/
theorem field_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (branches : ∀ (q : ℚ[X]) (hq : Prime q), BranchAt labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (signPattern (labels σ)) z) :=
  CenteredContactReconstruction318.field_reconstruction labels
    (fun q hq => toCentered labels q hq (branches q hq))
/-- The entire field reconstruction now consumes only the actual original
labeled Galois field and its full geometric branch locus; every algebraic
normal/local/valuation input is constructed internally. -/
theorem field_of_branch_locus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : BranchLocus labels) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (signPattern (labels σ)) z) :=
  field_reconstruction labels (chooseBranch labels h)
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

include hbase hcover hnormal in
/-- Whole ORIGINAL candidate-curve endpoint, not just an abstract isomorphic
function field. Genuine PEL field/curve and full labeled branch inertia remain. -/
theorem original_curve_reconstruction
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (branches : ∀ (q : ℚ[X]) (hq : Prime q), BranchAt labels q hq) :
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
    (fun q hq => toCentered labels q hq (branches q hq))
include hbase hcover hnormal in
/-- Original whole-curve identification from a genuine whole branch-locus
statement, without a family of supplied local rings or selected primes. -/
theorem original_curve_of_branch_locus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : BranchLocus labels) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (signPattern (labels σ)) z) :=
  original_curve_reconstruction g p hbase V hcover hnormal labels (chooseBranch labels h)
end Curves
end OriginalFullInertiaReconstruction318
