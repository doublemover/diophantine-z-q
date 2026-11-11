module
public import PELOriginalProperSmoothGroup318
public section
noncomputable section
namespace PELOriginalIntegerMultiplication318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemePointGroup318
open PELOriginalTorusPointAddEquiv318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The universal point of the ORIGINAL representing scheme. -/
@[expose] def identityPoint : Points τ hτ (candidate τ hτ) (π τ hτ) :=
  ⟨𝟙 _,Category.id_comp _⟩

/-- Genuine regular multiplication by an arbitrary integer, extracted
from the represented group at its universal point. It uses the actual
addition/inverse scheme maps, not a transported analytic endomorphism. -/
@[expose] def multiplication (n : ℤ) : candidate τ hτ ⟶ candidate τ hτ :=
  (n • identityPoint τ hτ).val

@[reassoc] lemma over_complex (n : ℤ) : multiplication τ hτ n≫π τ hτ=π τ hτ :=
  (n • identityPoint τ hτ).property

lemma pull_identityPoint {Y : Scheme} {ρ : Y ⟶ Spec (CommRingCat.of ℂ)}
    (p : Y ⟶ candidate τ hτ) (hp : p≫π τ hτ=ρ) :
    pull τ hτ (π τ hτ) p hp (identityPoint τ hτ)=⟨p,hp⟩ := by
  apply Subtype.ext
  exact Category.comp_id p

/-- Multiplication represents integer scaling on EVERY scheme-valued
point, including all nonreduced and infinitesimal test schemes. -/
theorem test_action (n : ℤ) {Y : Scheme} {ρ : Y ⟶ Spec (CommRingCat.of ℂ)}
    (p : Y ⟶ candidate τ hτ) (hp : p≫π τ hτ=ρ) :
    p≫multiplication τ hτ n=(n • (⟨p,hp⟩ : Points τ hτ Y ρ)).val := by
  have h := congrArg Subtype.val
    (map_zsmul (pull τ hτ (π τ hτ) p hp) (identityPoint τ hτ) n)
  rw [pull_identityPoint] at h
  exact h

/-- Exact original torus multiplication at EVERY original point. -/
theorem original_action (n : ℤ) (q : Base τ) :
    candidateComplexPoint τ hτ q≫multiplication τ hτ n=candidateComplexPoint τ hτ (n • q) := by
  calc
    _=(n • originalPoints τ hτ q).val :=
      test_action τ hτ n _ (PELOriginalProperComplexCandidate318.candidate_point_over τ hτ q)
    _=(originalPoints τ hτ (n • q)).val :=
      congrArg Subtype.val (map_zsmul (originalPoints τ hτ) q n).symm
    _=_ := rfl
end PELOriginalIntegerMultiplication318
