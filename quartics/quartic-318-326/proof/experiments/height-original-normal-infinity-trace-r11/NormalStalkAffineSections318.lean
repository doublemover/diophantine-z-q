module
public import NormalizationBirationalComparison318
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public section
noncomputable section
namespace NormalStalkAffineSections318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{u}) [IsIntegral X]
  (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

include hn in
/-- Normality of the ACTUAL section ring is produced from actual stalks
by maximal-localization descent. No normal affine cover is an extra input. -/
theorem sections (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X,U) := by
  let (x : PrimeSpectrum Γ(X,U)) :
      Algebra Γ(X,U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X,U)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P,hP⟩)) P :=
    hU.isLocalization_stalk' ⟨P,hP⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun P hP => X.presheaf.stalk (hU.fromSpec ⟨P,hP.isPrime⟩))
    (fun P _ => hn _)

variable {X} {Y B : Scheme.{u}} [IsIntegral Y]
  (j : X ⟶ Y) (p : Y ⟶ B) [IsDominant j] [IsIntegralHom p]
  [QuasiCompact (j ≫ p)] [QuasiSeparated (j ≫ p)]
  [IsIso (DominantFunctionField318.map j)]

/-- The genuine normalization comparison is an isomorphism from the
target's given stalk normality, without assuming section normality. -/
theorem comparison_isIso
    (hnormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso (NormalizationBirationalComparison318.comparison j p) := by
  letI := NormalizationBirationalComparison318.comparison_generic j p
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨U,hU,hy,_⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  letI : Nonempty U := ⟨⟨y,hy⟩⟩
  letI := sections Y hnormal U hU
  exact ⟨U,hy,IntegralGenericIso318.restrict_isIso
    (NormalizationBirationalComparison318.comparison j p) U hU⟩
end NormalStalkAffineSections318
