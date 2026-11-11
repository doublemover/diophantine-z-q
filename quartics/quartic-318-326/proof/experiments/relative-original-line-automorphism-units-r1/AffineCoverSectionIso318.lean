module
public import OpenUnitSectionMap318
public import AffineLineUnitSectionIso318
public import ModuleFrameDescent318
public import RestrictedMapBijective318
public section
noncomputable section
namespace AffineCoverSectionIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (L : Line X) (s : Γ(L.object,⊤))
  {ι : Type u} (A : ι → CommRingCat.{u}) (j : ∀ i,Spec (A i) ⟶ X)
  [∀ i,IsOpenImmersion (j i)]

lemma local_iff (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (j i)).map
      (ModuleGlobalSections318.ofTop L.object s)) ↔
    OriginalAffineSectionZero318.ideal (A i) (LineSheafPullback318.line (j i) L)
      (OriginalOpenPullbackSections318.sectionPull (j i) L.object s)=⊤ :=
  (OpenUnitSectionMap318.isIso_iff (j i) L.object s).trans
    (AffineLineUnitSectionIso318.iff_ideal_top (A i) (LineSheafPullback318.line (j i) L) _)

/-- The actual whole-map isomorphism criterion on a complete original
open affine cover, retaining every original section and every full ideal. -/
lemma iff_ideals (hc : ⊤≤⨆i,(j i).opensRange) :
    IsIso (ModuleGlobalSections318.ofTop L.object s) ↔
    ∀ i,OriginalAffineSectionZero318.ideal (A i) (LineSheafPullback318.line (j i) L)
      (OriginalOpenPullbackSections318.sectionPull (j i) L.object s)=⊤ := by
  constructor
  · intro h i
    letI := h
    exact (local_iff L s A j i).mp inferInstance
  · intro h
    apply ModuleFrameDescent318.isIso_of_cover (fun i => (j i) ''ᵁ ⊤)
      (by simpa only [Scheme.Hom.image_top_eq_opensRange] using hc)
    intro i V hV
    letI := (local_iff L s A j i).mpr (h i)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (RestrictedMapBijective318.bijective (j i) (ModuleGlobalSections318.ofTop L.object s) V hV)
end AffineCoverSectionIso318
