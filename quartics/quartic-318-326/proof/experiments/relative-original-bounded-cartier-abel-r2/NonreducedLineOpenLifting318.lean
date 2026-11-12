module
public import NonreducedAffineLineLifting318
public section
noncomputable section
namespace NonreducedLineOpenLifting318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open TopologicalSpace Opposite LocalSheafCohomologySections318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original additive restriction retains the actual pulled-back kernel
line over an arbitrary affine ring, not merely a reduced test ring. -/
theorem surjective_image {R : CommRingCat.{0}} {X : Scheme.{0}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (L : Line X)
    (S : ShortComplex (ASheaf (X:=X))) (hS : S.ShortExact)
    (e : S.X₁ ≅ NonreducedLineRestriction318.additive L) :
    Function.Surjective (S.g.hom.app (op (f ''ᵁ ⊤))) := by
  let F := OpenImmersionAdditiveRestriction318.restriction f
  let := OpenImmersionAdditiveRestriction318.restriction_limits f
  let := OpenImmersionAdditiveRestriction318.restriction_colimits f
  let := OpenImmersionAdditiveRestriction318.restriction_additive f
  exact NonreducedAffineLineLifting318.surjective (LineSheafPullback318.line f L)
    (S.map F) (hS.map_of_exact F)
    (F.mapIso e ≪≫ NonreducedLineRestriction318.pullbackIso f L)

/-- Section lifting for the SAME original line on every actual affine
open of ANY scheme. Empty opens are included by the arbitrary-ring affine
argument, rather than excluded by a domain hypothesis. -/
theorem surjective_affine {X : Scheme.{0}} (L : Line X)
    (S : ShortComplex (ASheaf (X:=X))) (hS : S.ShortExact)
    (e : S.X₁ ≅ NonreducedLineRestriction318.additive L)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.hom.app (op U)) := by
  have h := surjective_image hU.fromSpec L S hS e
  have heq : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  rw [heq] at h
  exact h
end NonreducedLineOpenLifting318
