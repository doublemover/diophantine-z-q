module
public import OpenImmersionAdditiveRestriction318
public import NonreducedAffineSectionLifting318
public section
noncomputable section
namespace NonreducedOpenStructureLifting318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StructureAdditiveSheaf318
abbrev ASheaf (X : Scheme.{0}) := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual kernel comparison preserves arbitrary-affine section lifting. -/
theorem surjective_of_kernel_iso {Y : Scheme.{0}} [IsAffine Y]
    (S : ShortComplex (ASheaf Y)) (hS : S.ShortExact)
    (e : S.X₁ ≅ sheaf Y) : Function.Surjective (S.g.hom.app (op ⊤)) := by
  let m := e.inv ≫ S.f
  have hw : m ≫ S.g = 0 := by simp [m,S.zero]
  let T := ShortComplex.mk m S.g hw
  let φ : T ≅ S := ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)
    (by simp [T,m]) (by simp [T])
  exact NonreducedAffineSectionLifting318.surjective m S.g hw
    (ShortComplex.shortExact_of_iso φ.symm hS)

/-- Restriction retains the ORIGINAL structure-sheaf kernel and exact
sequence on the entire image of an arbitrary affine open immersion. -/
theorem surjective_image {Y X : Scheme.{0}} [IsAffine Y]
    (f : Y ⟶ X) [IsOpenImmersion f]
    (S : ShortComplex (ASheaf X)) (hS : S.ShortExact) (e : S.X₁ ≅ sheaf X) :
    Function.Surjective (S.g.hom.app (op (f ''ᵁ ⊤))) := by
  let L := OpenImmersionAdditiveRestriction318.restriction f
  let := OpenImmersionAdditiveRestriction318.restriction_limits f
  let := OpenImmersionAdditiveRestriction318.restriction_colimits f
  let := OpenImmersionAdditiveRestriction318.restriction_additive f
  exact surjective_of_kernel_iso (S.map L) (hS.map_of_exact L)
    (L.mapIso e ≪≫ OpenImmersionAdditiveRestriction318.structureIso f)

/-- Original section lifting on every affine open of ANY scheme, including
empty opens, without integral or reduced hypotheses. -/
theorem surjective_affine {X : Scheme.{0}}
    (S : ShortComplex (ASheaf X)) (hS : S.ShortExact) (e : S.X₁ ≅ sheaf X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.hom.app (op U)) := by
  have h := surjective_image hU.fromSpec S hS e
  have heq : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  rw [heq] at h
  exact h
end NonreducedOpenStructureLifting318
