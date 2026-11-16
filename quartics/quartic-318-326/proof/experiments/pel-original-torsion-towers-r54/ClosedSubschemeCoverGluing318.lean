module
public import OpenPullbackFamilyGluing318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ClosedSubschemeCoverGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (Z : ι → Scheme.{u})
  (z : ∀ i,Z i ⟶ (U i).toScheme) [∀ i,IsClosedImmersion (z i)]
@[expose] def localMap (i : ι) : Z i ⟶ X := z i≫(U i).ι
local instance localMap_mono (i : ι) : Mono (localMap U Z z i) := by
  dsimp [localMap]
  infer_instance
variable [∀ i j,IsOpenImmersion (pullback.fst (localMap U Z z i) (localMap U Z z j))]
  (hRange : ∀ i j,Set.range (pullback.fst (localMap U Z z i) (localMap U Z z j))=
    (localMap U Z z i) ⁻¹' (U j : Set X))
  (hCover : (⊤ : X.Opens) ≤ ⨆ i,U i)
abbrev Glued := OpenPullbackFamilyGluing318.Glued Z (localMap U Z z)
abbrev inclusion (i : ι) : Z i ⟶ Glued U Z z := OpenPullbackFamilyGluing318.inclusion Z (localMap U Z z) i
abbrev into : Glued U Z z ⟶ X := OpenPullbackFamilyGluing318.into Z (localMap U Z z)

include hRange in
/-- Each glued local chart is EXACTLY the whole inverse image of its
ambient open, not merely a subset with the correct closed points. -/
lemma preimage (i : ι) : into U Z z ⁻¹ᵁ U i=(inclusion U Z z i).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,y,rfl⟩ := OpenPullbackFamilyGluing318.covers Z (localMap U Z z) x
    have hy : localMap U Z z j y∈U i := by
      simpa only [←Scheme.Hom.comp_apply,OpenPullbackFamilyGluing318.inclusion_into] using hx
    rw [←hRange j i] at hy
    obtain ⟨w,hw⟩ := hy
    refine ⟨pullback.snd _ _ w,?_⟩
    have hg := congrArg (fun f => f w)
      ((OpenPullbackFamilyGluing318.glueData Z (localMap U Z z)).glue_condition j i)
    simpa only [pullbackSymmetry_hom_comp_fst_assoc,Scheme.Hom.comp_apply,hw] using hg
  · rintro ⟨y,rfl⟩
    change into U Z z (inclusion U Z z i y)∈U i
    rw [←Scheme.Hom.comp_apply,OpenPullbackFamilyGluing318.inclusion_into]
    exact (z i y).property

include hRange in
lemma cartesian (i : ι) : IsPullback (z i) (inclusion U Z z i) (U i).ι (into U Z z) :=
  IsOpenImmersion.isPullback _ _ _ _
    (OpenPullbackFamilyGluing318.inclusion_into Z (localMap U Z z) i).symm
    (preimage U Z z hRange i)

@[expose] def ambientCover : X.OpenCover where
  I₀ := ι
  X i := (U i).toScheme
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hCover (show x∈⊤ from trivial))
      exact ⟨i,⟨x,hi⟩,rfl⟩
    · infer_instance

include hRange hCover in
/-- Actual global closed immersion. Local principal quotients, including
their multiplicities, are the genuine full scheme-theoretic base changes. -/
theorem closed : IsClosedImmersion (into U Z z) := by
  apply IsZariskiLocalAtTarget.of_openCover (ambientCover U hCover)
  intro i
  have h := (cartesian U Z z hRange i).flip
  have hc : IsClosedImmersion (h.isoPullback.inv≫z i) := inferInstance
  simpa only [h.isoPullback_inv_snd] using hc
end ClosedSubschemeCoverGluing318
