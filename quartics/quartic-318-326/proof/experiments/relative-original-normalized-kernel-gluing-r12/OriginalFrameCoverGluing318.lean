module
public import OriginalFrameCoverSections318
public section
noncomputable section
namespace OriginalFrameCoverGluing318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFrameCoverSections318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤) (e : LocalFrames L Y j) (he : Compatible L Y j e)
@[expose] def globalSection : Γ(L.object,⊤) :=
  ModuleGlobalSections318.gluedTop L.object (fun i => (j i) ''ᵁ ⊤) hc (pieces L Y j e) he
lemma section_restrict (i : ι) :
    L.object.presheaf.map (homOfLE (show (j i) ''ᵁ ⊤≤⊤ from le_top)).op
      (globalSection L Y j hc e he)=pieces L Y j e i :=
  ModuleGlobalSections318.gluedTop_restrict L.object _ hc _ he i
lemma section_pull (i : ι) :
    OriginalOpenPullbackSections318.sectionPull (j i) L.object (globalSection L Y j hc e he)=
      (e i).hom.app ⊤ 1 := by
  apply (OriginalOpenPullbackSections318.sectionsEquiv (j i) L.object).injective
  rw [OriginalOpenPullbackSections318.unit_sections]
  exact section_restrict L Y j hc e he i
lemma local_isIso (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (j i)).map
    (ModuleGlobalSections318.ofTop L.object (globalSection L Y j hc e he))) := by
  apply (OpenUnitSectionMap318.isIso_iff (j i) L.object _).mpr
  rw [section_pull,←ModuleTopExt318.eq_ofTop (e i).hom]
  infer_instance
lemma global_isIso : IsIso (ModuleGlobalSections318.ofTop L.object (globalSection L Y j hc e he)) := by
  apply ModuleFrameDescent318.isIso_of_cover (fun i => (j i) ''ᵁ ⊤) hc
  intro i V hV
  letI := local_isIso L Y j hc e he i
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (RestrictedMapBijective318.bijective (j i)
      (ModuleGlobalSections318.ofTop L.object (globalSection L Y j hc e he)) V hV)
/-- The glued frame has the SAME glued original section as its forward
map. The inverse is supplied only after actual full-cover isomorphism descent. -/
@[expose] def frame : Frames L := by
  letI := global_isIso L Y j hc e he
  exact asIso (ModuleGlobalSections318.ofTop L.object (globalSection L Y j hc e he))
lemma value : (frame L Y j hc e he).hom.app ⊤ 1=globalSection L Y j hc e he :=
  ModuleTopMorphisms318.ofTop_top_one _
lemma frame_restrict (i : ι) : restrict L Y j (frame L Y j hc e he) i=e i := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change (OriginalFramePullback318.frame (j i) L (frame L Y j hc e he)).hom.app ⊤ 1=_
  rw [OriginalFramePullback318.value,value]
  exact section_pull L Y j hc e he i
end OriginalFrameCoverGluing318
