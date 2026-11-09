module
public import NormalBasisCharacterRadicals318
public import FourBinaryCharacters318
public import ContactDivisorFieldReconstruction318
public import ComplementaryFunctionRigidity318
public section
noncomputable section
open scoped BigOperators
namespace GaloisCharacterContactReconstruction318
variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
variable (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)

/-- This consumes an actual labeled Galois-group isomorphism, not an abstract
assertion that four symbols denote involutions. -/
@[expose] def character (i : Fin 4) : (L ≃ₐ[RatFunc ℚ] L) →* RatFunc ℚ :=
  (FourBinaryCharacters318.complementary i).comp labels.toMonoidHom

lemma character_square (i : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) : character labels i σ ^ 2 = 1 :=
  FourBinaryCharacters318.complementary_square i (labels σ)

lemma character_nontrivial (i : Fin 4) : ∃ σ, character labels i σ ≠ 1 := by
  obtain ⟨w, hw⟩ := FourBinaryCharacters318.complementary_nontrivial (F := RatFunc ℚ) i
  refine ⟨labels.symm w, ?_⟩
  simpa only [character, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    labels.apply_symm_apply] using hw

@[expose] def root (i : Fin 4) : L := NormalBasisCharacterRadicals318.root (character labels i)
@[expose] def radicand (i : Fin 4) : RatFunc ℚ :=
  NormalBasisCharacterRadicals318.radicand (character labels i) (character_square labels i)

lemma root_square (i : Fin 4) : root labels i ^ 2 = algebraMap (RatFunc ℚ) L (radicand labels i) :=
  NormalBasisCharacterRadicals318.root_square _ _
lemma radicand_ne_zero (i : Fin 4) : radicand labels i ≠ 0 :=
  NormalBasisCharacterRadicals318.radicand_ne_zero _ _
lemma radicand_nonsquare (i : Fin 4) : ¬ IsSquare (radicand labels i) :=
  NormalBasisCharacterRadicals318.radicand_nonsquare _ _ (character_nontrivial labels i)
lemma root_action (i : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) :
    σ (root labels i) = character labels i σ • root labels i :=
  NormalBasisCharacterRadicals318.root_action _ (character_square labels i) σ

/-- Degree16 is now derived from the actual Galois group, not supplied separately. -/
theorem degree : Module.finrank (RatFunc ℚ) L = 16 := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr labels.toEquiv).trans FourBinaryCharacters318.card

/-- The candidate's actual Galois action constructs ALL four nonzero quadratic
character functions and its degree. The remaining input is precisely their
original branch parity, quantified at every closed finite point. -/
theorem reconstruct
    (hparity : ∀ i (q : Polynomial ℚ), Prime q →
      Even (RationalFunctionEvenSquare318.orderAt q
        (radicand labels i / ContactDivisorFieldReconstruction318.contactProduct i))) :
    ∃ c : Fin 4 → ℚˣ, ∃ u : Fin 4 → RatFunc ℚ, (∀ i, u i ≠ 0) ∧
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ i, e (FourRootEvaluation318.characterGenerator (SourceKummerField318.parameter c) i) *
          algebraMap (RatFunc ℚ) L (u i) = root labels i :=
  ContactDivisorFieldReconstruction318.reconstruct (radicand labels) (radicand_ne_zero labels)
    (root labels) (root_square labels) (degree labels) hparity
lemma sign_coefficient (i : Fin 4) (σ : L ≃ₐ[RatFunc ℚ] L) :
    ComplementSquareclass318.complementaryProduct
      (ComplementRootAction318.sign (FourBinaryCharacters318.signPattern (labels σ))) i =
        character labels i σ := by
  simp [ComplementSquareclass318.complementaryProduct, ComplementRootAction318.sign,
    FourBinaryCharacters318.signPattern, FourBinaryCharacters318.complementary,
    FourBinaryCharacters318.coordinate, character]

/-- The same branch-reconstructed equivalence intertwines EVERY original
Galois automorphism with the original root-sign action in the supplied labels. -/
theorem reconstruct_equivariant
    (hparity : ∀ i (q : Polynomial ℚ), Prime q →
      Even (RationalFunctionEvenSquare318.orderAt q
        (radicand labels i / ContactDivisorFieldReconstruction318.contactProduct i))) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (FourBinaryCharacters318.signPattern (labels σ)) z) := by
  obtain ⟨c, u, hu, e, he⟩ := reconstruct labels hparity
  refine ⟨c, e, ?_⟩
  intro σ z
  refine ComplementaryFunctionRigidity318.equivariant _
    (LabeledContactFieldReconstruction318.parameter_ne_zero c) e u hu (root labels) he σ
      (FourBinaryCharacters318.signPattern (labels σ)) ?_ z
  intro i
  rw [sign_coefficient, root_action, Algebra.smul_def]
end GaloisCharacterContactReconstruction318
