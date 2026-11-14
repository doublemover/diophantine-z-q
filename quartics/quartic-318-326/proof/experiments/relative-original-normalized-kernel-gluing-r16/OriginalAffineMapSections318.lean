module
public import OriginalLineAffineBaseChange318
public import PullbackPathComposition318

public section
noncomputable section
namespace OriginalAffineMapSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- Exact ring map of an arbitrary original affine scheme map into Spec R. -/
def ringMap : R ⟶ Γ(X,⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop

lemma specMap : Spec.map (ringMap f) = X.isoSpec.inv ≫ f := by
  rw [ringMap,Spec.map_comp,← Scheme.isoSpec_Spec_inv,Scheme.isoSpec_inv_naturality]

variable (L : Line (Spec R))

/-- Original affine base change followed by the proved literal affine map
comparison and actual pullback composition. -/
def sheafIso :
    tilde (OriginalLineAffineBaseChange318.extendedSections (ringMap f) L) ≅
      (Scheme.Modules.pullback X.isoSpec.inv).obj ((Scheme.Modules.pullback f).obj L.object) :=
  OriginalLineAffineBaseChange318.sheafIso (ringMap f) L ≪≫
    (Scheme.Modules.pullbackCongr (specMap f)).app L.object ≪≫
    ((Scheme.Modules.pullbackComp X.isoSpec.inv f).app L.object).symm

/-- The genuine scalar extension of the OLD original line sections is
identified with the original actual pullback's affine sections. -/
@[expose] def sectionsIso : OriginalLineAffineBaseChange318.extendedSections (ringMap f) L ≅
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback X.isoSpec.inv).obj
      ((Scheme.Modules.pullback f).obj L.object)) :=
  tilde.isoTop _ ≪≫ moduleSpecΓFunctor.mapIso (sheafIso f L)

lemma sectionsIso_hom : (sectionsIso f L).hom =
    (tilde.isoTop _).hom ≫ moduleSpecΓFunctor.map (sheafIso f L).hom := rfl
end OriginalAffineMapSections318
