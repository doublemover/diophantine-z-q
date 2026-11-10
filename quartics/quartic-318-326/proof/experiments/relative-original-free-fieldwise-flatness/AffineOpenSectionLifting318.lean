module
public import OpenImmersionAdditiveRestriction318
public import AffineStructureSectionLifting318
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Category.Grp.Zero

public section
noncomputable section
namespace AffineOpenSectionLifting318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StructureAdditiveSheaf318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev ASheaf (X : Scheme.{0}) := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

/-- Affine section lifting is unchanged under an isomorphism of the actual kernel sheaf. -/
theorem surjective_of_kernel_iso {R : CommRingCat.{0}} [IsDomain R]
    (S : ShortComplex (ASheaf (Spec R))) (hS : S.ShortExact)
    (e : S.X₁ ≅ sheaf (Spec R)) : Function.Surjective (S.g.hom.app (op ⊤)) := by
  let m := e.inv ≫ S.f
  have hw : m ≫ S.g = 0 := by simp [m,S.zero]
  let T := ShortComplex.mk m S.g hw
  let φ : T ≅ S := ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)
    (by simp [T,m]) (by simp [T])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso φ.symm hS
  exact AffineStructureSectionLifting318.surjective m S.g hw hT

/-- Lifting on the original image of an affine open immersion from Spec of a domain. -/
theorem surjective_image {R : CommRingCat.{0}} [IsDomain R] {X : Scheme.{0}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (S : ShortComplex (ASheaf X))
    (hS : S.ShortExact) (e : S.X₁ ≅ sheaf X) :
    Function.Surjective (S.g.hom.app (op (f ''ᵁ ⊤))) := by
  let L := OpenImmersionAdditiveRestriction318.restriction f
  let := OpenImmersionAdditiveRestriction318.restriction_limits f
  let := OpenImmersionAdditiveRestriction318.restriction_colimits f
  let := OpenImmersionAdditiveRestriction318.restriction_additive f
  exact surjective_of_kernel_iso (S.map L) (hS.map_of_exact L)
    (L.mapIso e ≪≫ OpenImmersionAdditiveRestriction318.structureIso f)

/-- Section lifting over every nonempty affine open of the original integral scheme. -/
theorem surjective_affine {X : Scheme.{0}} [IsIntegral X]
    (S : ShortComplex (ASheaf X)) (hS : S.ShortExact) (e : S.X₁ ≅ sheaf X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Surjective (S.g.hom.app (op U)) := by
  have h := surjective_image hU.fromSpec S hS e
  have heq : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  rw [heq] at h
  exact h

/-- Empty affine opens are handled by the actual sheaf empty-section condition. -/
theorem surjective_affine_all {X : Scheme.{0}} [IsIntegral X]
    (S : ShortComplex (ASheaf X)) (hS : S.ShortExact) (e : S.X₁ ≅ sheaf X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.hom.app (op U)) := by
  classical
  by_cases hn : Nonempty U
  · let := hn
    exact surjective_affine S hS e U hU
  · have he : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hn ⟨⟨x,hx⟩⟩).elim
      · simp
    have hz : IsZero (S.X₃.obj.obj (op U)) := (IsZero.iff_id_eq_zero _).mpr
      ((TopCat.Sheaf.isTerminalOfEqEmpty S.X₃ he).hom_ext _ _)
    let := AddCommGrpCat.subsingleton_of_isZero hz
    intro t
    exact ⟨0,Subsingleton.elim _ _⟩

end AffineOpenSectionLifting318
