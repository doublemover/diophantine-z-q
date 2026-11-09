module
public import UniversalStructurePushforward318
public import ActualSourceRationalConstants318
public section
noncomputable section
namespace ContactUniversalGlobalFunctions318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X := ActualSourceRationalConstants318.X
abbrev p := ActualSourceRationalConstants318.p
abbrev Base := Spec (CommRingCat.of ℚ)

instance sourceProper : IsProper p :=
  (ContactGlobalProper318.proper_integral_extension SourceTwistArithmetic318.units).2.2

/-- The established original structural-Q constant theorem makes the
original structure morphism's actual global-section map an isomorphism. -/
instance source_appTop_isIso : IsIso p.appTop := by
  have hi : IsIso ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ p.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ActualSourceRationalConstants318.constant_bijective
  exact (isIso_comp_left_iff _ _).mp hi

/-- Universal actual structure-sheaf pushforward for every scheme test
over Q, including nonreduced and nonquasicompact tests. -/
lemma structureMorphism_isIso {T : Scheme} (b : T ⟶ Base) :
    IsIso (UniversalStructurePushforward318.structureMorphism (pullback.snd p b)) :=
  UniversalStructurePushforward318.baseChange_structureMorphism_isIso p b

/-- This is the exact original structure map on every full inverse-image
open, with no affine or reduced test restriction. -/
lemma app_isIso {T : Scheme} (b : T ⟶ Base) (U : T.Opens) :
    IsIso ((pullback.snd p b).app U) :=
  UniversalStructurePushforward318.baseChange_app_isIso p b U

lemma app_bijective {T : Scheme} (b : T ⟶ Base) (U : T.Opens) :
    Function.Bijective ((pullback.snd p b).app U) := by
  let := app_isIso b U
  exact ConcreteCategory.bijective_of_isIso _
end ContactUniversalGlobalFunctions318
