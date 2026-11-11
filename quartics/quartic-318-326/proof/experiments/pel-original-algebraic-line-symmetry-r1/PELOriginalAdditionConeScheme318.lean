module
public import PELOriginalAdditionConeRelations318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace PELOriginalAdditionConeScheme318
open AlgebraicGeometry CategoryTheory
open PELOriginalAdditionConeRelations318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Evaluation of the ENTIRE actual relation quotient at an original scaled
Segre pair. Every relation vanishes by the independent kernel definition. -/
@[expose] def pointEvaluation (N : ℕ) [NeZero N] (p : Parameters) :
    ConeRing τ hτ N →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (relations τ hτ N) (evaluation τ hτ N p)
    (fun f hf => (mem_relations τ hτ N f).mp hf p)

lemma pointEvaluation_mk (N : ℕ) [NeZero N] (p : Parameters) (f : Polynomials N) :
    pointEvaluation τ hτ N p (Ideal.Quotient.mk (relations τ hτ N) f) =
      evaluation τ hτ N p f := rfl

lemma point_square (p : Parameters) :
    (pointEvaluation τ hτ 6 p).comp (coneMap τ hτ) =
      pointEvaluation τ hτ 3 (sumDifference p) := by
  apply AlgHom.ext
  intro a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  change evaluation τ hτ 6 p (substitution τ hτ f) =
    evaluation τ hτ 3 (sumDifference p) f
  exact DFunLike.congr_fun (evaluation_square τ hτ p) f

abbrev ConeScheme (N : ℕ) [NeZero N] := Spec (CommRingCat.of (ConeRing τ hτ N))
@[expose] def structureMap (N : ℕ) [NeZero N] : ConeScheme τ hτ N ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (ConeRing τ hτ N)))

/-- An actual affine SCHEME morphism on the entire independent level-six
Segre relation model. This is not a transported map on complex point sets.
The separate cubic-product/level-six source comparison remains open. -/
@[expose] def additionSchemeMap : ConeScheme τ hτ 6 ⟶ ConeScheme τ hτ 3 :=
  Spec.map (CommRingCat.ofHom (coneMap τ hτ).toRingHom)

theorem addition_over_complex :
    additionSchemeMap τ hτ ≫ structureMap τ hτ 3 = structureMap τ hτ 6 := by
  unfold additionSchemeMap structureMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (coneMap τ hτ).commutes c

@[expose] def originalPoint (N : ℕ) [NeZero N] (p : Parameters) :
    Spec (CommRingCat.of ℂ) ⟶ ConeScheme τ hτ N :=
  Spec.map (CommRingCat.ofHom (pointEvaluation τ hτ N p).toRingHom)

/-- Genuine morphism equality for every actual original pair and every
cone scalar, retaining the literal sum and difference in the target. -/
theorem original_point_action (p : Parameters) :
    originalPoint τ hτ 6 p ≫ additionSchemeMap τ hτ =
      originalPoint τ hτ 3 (sumDifference p) := by
  unfold originalPoint additionSchemeMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (point_square τ hτ p)

/-- Every original cubic Segre cone point is reached by the actual scheme
map, by the explicit invertible half-sum/half-difference parameter change.
No assertion about all primes or arbitrary scheme-valued points is made. -/
theorem every_original_target_reached (p : Parameters) :
    ∃ q : Parameters, originalPoint τ hτ 6 q ≫ additionSchemeMap τ hτ =
      originalPoint τ hτ 3 p := by
  obtain ⟨q,rfl⟩ := sumDifference_surjective p
  exact ⟨q,original_point_action τ hτ q⟩
end PELOriginalAdditionConeScheme318
