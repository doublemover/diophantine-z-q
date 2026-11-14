module
public import FlatGlobalSections318
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public section
noncomputable section
namespace UniversalStructurePushforward318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S T : Scheme.{u}}

/-- The actual morphism from the base structure sheaf to the actual direct
image of the source structure sheaf, retaining every original restriction. -/
@[expose] def structureMorphism (p : X ⟶ S) : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat p.base).obj X.sheaf := ⟨p.c⟩

@[simp] lemma structureMorphism_app (p : X ⟶ S) (U : S.Opens) :
    (structureMorphism p).hom.app (op U) = p.app U := rfl

/-- Actual universal structure-sheaf pushforward along flat tests, from the
canonical affine-open comparisons and sheaf descent on the full basis. -/
lemma baseChange_structureMorphism_isIso (p : X ⟶ S) (b : T ⟶ S)
    [IsAffine S] [IsProper p] [Flat b] [IsIso p.appTop] :
    IsIso (structureMorphism (pullback.snd p b)) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : T.affineOpens => (U : T.Opens))
  · simpa only [Subtype.range_coe] using T.isBasis_affineOpens
  · intro U
    exact FlatGlobalSections318.baseChange_app_isIso p b U U.property

/-- Consequently the unchanged original structure map is an isomorphism
on every open, including nonaffine and nonquasicompact opens. -/
lemma baseChange_app_isIso (p : X ⟶ S) (b : T ⟶ S)
    [IsAffine S] [IsProper p] [Flat b] [IsIso p.appTop] (U : T.Opens) :
    IsIso ((pullback.snd p b).app U) := by
  let := baseChange_structureMorphism_isIso p b
  exact inferInstanceAs (IsIso ((structureMorphism (pullback.snd p b)).hom.app (op U)))
end UniversalStructurePushforward318
