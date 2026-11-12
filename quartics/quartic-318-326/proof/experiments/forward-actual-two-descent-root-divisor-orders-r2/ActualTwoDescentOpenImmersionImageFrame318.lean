module
public import ActualTwoDescentOriginalIdealEverywhereFramed318
public import AffinePrincipalLineFrame318
public section
noncomputable section
namespace ActualTwoDescentOpenImmersionImageFrame318
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

def imageIso : Y ≅ j.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
    change (j.opensRange : Set X)=Set.range j.opensRange.ι
    rw [Scheme.Opens.range_ι])
lemma imageIso_square : (imageIso j).hom ≫ j.opensRange.ι=j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Transfer an actual chart frame onto its exact ambient open image,
retaining the original module and the native restriction comparison. -/
def imageFrame (M : X.Modules)
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf ≅ M.restrict j.opensRange.ι :=
  AffinePrincipalLineFrame318.alongIso (imageIso j) (M.restrict j.opensRange.ι)
    (e.symm ≪≫ (Scheme.Modules.restrictFunctorCongr (imageIso_square j).symm).app M ≪≫
      (Scheme.Modules.restrictFunctorComp (imageIso j).hom j.opensRange.ι).app M)
end ActualTwoDescentOpenImmersionImageFrame318
