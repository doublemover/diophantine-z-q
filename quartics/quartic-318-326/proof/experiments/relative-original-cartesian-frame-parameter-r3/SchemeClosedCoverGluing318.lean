module
public import MonoFamilyGlueData318
public section
noncomputable section
namespace SchemeClosedCoverGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} (U : X.OpenCover) (Z : U.I₀ → Scheme.{u})
  (q : ∀ i, Z i ⟶ U.X i) [∀ i, IsClosedImmersion (q i)]
local notation "f" => fun i => q i ≫ U.f i
variable [∀ i j, IsOpenImmersion (pullback.fst (f i) (f j))]
  (H : ∀ i j, IsPullback (pullback.snd (f i) (f j))
    (pullback.fst (f i) (f j) ≫ q i) (f j) (U.f i))
/-- Every local closed family is the actual restriction of the glued
family. This uses genuine local ambient Cartesian squares, not just support. -/
lemma cartesian (i : U.I₀) : IsPullback (MonoFamilyGlueData318.into Z f i) (q i)
    (MonoFamilyGlueData318.map Z f) (U.f i) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (MonoFamilyGlueData318.cover Z f)
  intro j
  change IsPullback (pullback.snd (MonoFamilyGlueData318.into Z f i) (MonoFamilyGlueData318.into Z f j))
    (pullback.fst (MonoFamilyGlueData318.into Z f i) (MonoFamilyGlueData318.into Z f j) ≫ q i)
    (MonoFamilyGlueData318.into Z f j ≫ MonoFamilyGlueData318.map Z f) (U.f i)
  rw [MonoFamilyGlueData318.into_map]
  let h := MonoFamilyGlueData318.intersection Z f i j
  apply (H i j).of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
/-- The resulting original ambient map is genuinely globally closed. -/
lemma closed : IsClosedImmersion (MonoFamilyGlueData318.map Z f) := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro i
  have h := cartesian U Z q H i
  have hc : IsClosedImmersion (h.isoPullback.inv ≫ q i) := inferInstance
  simpa only [h.isoPullback_inv_snd] using hc
end SchemeClosedCoverGluing318
