module
public import LineSheafClass318
public section
noncomputable section
namespace LocalLineGlobalFrames318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Transport an original unit frame through an actual scheme isomorphism,
using original unit, composition, equality and identity comparisons. -/
@[expose] def unitAlongIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (M : Z.Modules)
    (frame : SheafOfModules.unit Y.ringCatSheaf ≅ M.restrict e.hom) :
    SheafOfModules.unit Z.ringCatSheaf ≅ M :=
  (Scheme.Modules.restrictUnitIso e.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso frame ≪≫
      (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm.app M ≪≫
        (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M ≪≫
          (Scheme.Modules.restrictFunctorId (X := Z)).app M

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (L : ∀ i, LineSheafClass318.Line (U i).toScheme) (M : X.Modules)
  (e : ∀ i, M.restrict (U i).ι ≅ (L i).object)

/-- Actual local line frames refine the original ambient chart family by
their original open images. -/
abbrev frameOpen (a : Σ i, (L i).Index) : X.Opens :=
  (U a.1).ι ''ᵁ (L a.1).opens a.2

/-- The local frame on its original open subscheme is carried to the
literal ambient image, without replacing the global module sheaf. -/
@[expose] def frame (a : Σ i, (L i).Index) :
    SheafOfModules.unit (frameOpen U L a).toScheme.ringCatSheaf ≅
      M.restrict (frameOpen U L a).ι := by
  let V := (L a.1).opens a.2
  let f := (U a.1).ι
  let k := f.isoImage V
  apply unitAlongIso k (M.restrict (frameOpen U L a).ι)
  exact (L a.1).frame a.2 ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso (e a.1).symm ≪≫
      (Scheme.Modules.restrictFunctorComp V.ι f).symm.app M ≪≫
        (Scheme.Modules.restrictFunctorCongr (f.isoImage_hom_ι V).symm).app M ≪≫
          (Scheme.Modules.restrictFunctorComp k.hom (frameOpen U L a).ι).app M

include e in
/-- The actual original local-line isomorphisms and original cover yield
an actual global framed line on the unchanged module sheaf. -/
@[expose] def line (hcover : (⊤ : X.Opens) ≤ iSup U) : LineSheafClass318.Line X where
  object := M
  Index := Σ i, (L i).Index
  opens := frameOpen U L
  cover := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hx)
    let y : (U i).toScheme := ⟨x, hi⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((L i).cover (show y ∈ (⊤ : (U i).toScheme.Opens) from trivial))
    apply Opens.mem_iSup.mpr
    exact ⟨⟨i, j⟩, ⟨y, hj, rfl⟩⟩
  frame := frame U L M e
end LocalLineGlobalFrames318
