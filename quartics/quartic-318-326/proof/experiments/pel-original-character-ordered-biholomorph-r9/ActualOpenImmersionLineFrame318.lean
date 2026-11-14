module
public import LineSheafClass318
public section
noncomputable section
namespace ActualOpenImmersionLineFrame318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y:Scheme.{u}} (j:X⟶Y) [IsOpenImmersion j]
/-- The actual original chart is isomorphic to its actual ambient open
image. This is not a replacement by an abstract same-field affine chart. -/
@[expose] def imageIso:X≅j.opensRange.toScheme:=
  IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
    rw [Scheme.Opens.range_ι]
    rfl)
lemma image_square:(imageIso j).hom≫j.opensRange.ι=j:=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
@[expose] def alongIso {A B:Scheme.{u}} (e:A≅B) (M:B.Modules)
    (frame:SheafOfModules.unit A.ringCatSheaf≅M.restrict e.hom):
    SheafOfModules.unit B.ringCatSheaf≅M:=
  (Scheme.Modules.restrictUnitIso e.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso frame ≪≫
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm.app M) ≪≫
    ((Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M) ≪≫
    ((Scheme.Modules.restrictFunctorId (X:=B)).app M)
/-- The unchanged ambient module sheaf acquires its rank-one frame on
its genuine ambient open, via the actual open-immersion square. -/
@[expose] def ambientFrame (M:Y.Modules)
    (frame:SheafOfModules.unit X.ringCatSheaf≅M.restrict j):
    SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf≅M.restrict j.opensRange.ι:=
  alongIso (imageIso j) (M.restrict j.opensRange.ι)
    (frame ≪≫
      ((Scheme.Modules.restrictFunctorCongr (image_square j).symm).app M) ≪≫
      ((Scheme.Modules.restrictFunctorComp (imageIso j).hom j.opensRange.ι).app M))
end ActualOpenImmersionLineFrame318
