module
public import OriginalAffineLineSectionLifting318
public section
noncomputable section
namespace OriginalLineOpenSectionLifting318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open TopologicalSpace Opposite LocalSheafCohomologySections318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restrict the actual short exact sequence to the original image of an
open affine chart and retain its SAME actual pulled-back kernel line. -/
theorem surjective_image {R : CommRingCat.{0}} [IsDomain R] {X : Scheme.{0}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (L : Line X)
    (S : ShortComplex (ASheaf (X:=X))) (hS : S.ShortExact)
    (e : S.X₁ ≅ OriginalLineRestrictionAdditive318.additive L) :
    Function.Surjective (S.g.hom.app (op (f ''ᵁ ⊤))) := by
  let F := OpenImmersionAdditiveRestriction318.restriction f
  let := OpenImmersionAdditiveRestriction318.restriction_limits f
  let := OpenImmersionAdditiveRestriction318.restriction_colimits f
  let := OpenImmersionAdditiveRestriction318.restriction_additive f
  exact OriginalAffineLineSectionLifting318.surjective (LineSheafPullback318.line f L)
    (S.map F) (hS.map_of_exact F)
    (F.mapIso e ≪≫ OriginalLineRestrictionAdditive318.pullbackIso f L)

/-- Every actual affine open of the original integral scheme, including the
empty open, has section lifting for exact sequences with the original line
as kernel. The line itself has not been replaced or globally trivialized. -/
theorem surjective_affine {X : Scheme.{0}} [IsIntegral X] (L : Line X)
    (S : ShortComplex (ASheaf (X:=X))) (hS : S.ShortExact)
    (e : S.X₁ ≅ OriginalLineRestrictionAdditive318.additive L)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.hom.app (op U)) := by
  classical
  by_cases hn : Nonempty U
  · letI := hn
    have h := surjective_image hU.fromSpec L S hS e
    have heq : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) = U :=
      hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
    rw [heq] at h
    exact h
  · have he : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hn ⟨⟨x,hx⟩⟩).elim
      · simp
    have hz : IsZero (S.X₃.obj.obj (op U)) := (IsZero.iff_id_eq_zero _).mpr
      ((TopCat.Sheaf.isTerminalOfEqEmpty S.X₃ he).hom_ext _ _)
    letI := AddCommGrpCat.subsingleton_of_isZero hz
    intro t
    exact ⟨0,Subsingleton.elim _ _⟩
end OriginalLineOpenSectionLifting318
