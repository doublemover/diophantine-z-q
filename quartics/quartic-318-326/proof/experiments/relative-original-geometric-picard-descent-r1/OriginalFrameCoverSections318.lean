module
public import OriginalFramePullbackCoherence318
public import AffineCoverSectionIso318
public section
noncomputable section
namespace OriginalFrameCoverSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤)
abbrev LocalFrames := ∀ i,Frames (LineSheafPullback318.line (j i) L)
@[expose] def pieces (e : LocalFrames L Y j) (i : ι) : Γ(L.object,(j i) ''ᵁ ⊤) :=
  OriginalOpenPullbackSections318.sectionsEquiv (j i) L.object ((e i).hom.app ⊤ 1)
abbrev Compatible (e : LocalFrames L Y j) :=
  TopCat.Presheaf.IsCompatible L.object.presheaf (fun i => (j i) ''ᵁ ⊤) (pieces L Y j e)
@[expose] def restrict (e : Frames L) : LocalFrames L Y j :=
  fun i => OriginalFramePullback318.frame (j i) L e
lemma restrict_value (e : Frames L) (i : ι) :
    pieces L Y j (restrict L Y j e) i=
      L.object.presheaf.map (homOfLE (show (j i) ''ᵁ ⊤≤⊤ from le_top)).op
        (e.hom.app ⊤ 1) := by
  unfold pieces restrict
  rw [OriginalFramePullback318.value]
  exact OriginalOpenPullbackSections318.unit_sections (j i) L.object (e.hom.app ⊤ 1)
lemma restrict_compatible (e : Frames L) : Compatible L Y j (restrict L Y j e) := by
  intro i k
  rw [restrict_value,restrict_value,←Functor.map_comp_apply,←Functor.map_comp_apply]
  rfl
include hc in
/-- Actual full frames are separated on a covering family of open maps;
no affine, reduced, finite-type or field assumption is used. -/
lemma ext (e d : Frames L) (h : ∀ i,restrict L Y j e i=restrict L Y j d i) : e=d := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.object.presheaf,L.object.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i => (j i) ''ᵁ ⊤) ⊤ (fun _ => homOfLE le_top) hc
  intro i
  rw [←restrict_value,←restrict_value]
  exact congrArg (fun q => OriginalOpenPullbackSections318.sectionsEquiv (j i) L.object
    (q.hom.app ⊤ 1)) (h i)
end OriginalFrameCoverSections318
