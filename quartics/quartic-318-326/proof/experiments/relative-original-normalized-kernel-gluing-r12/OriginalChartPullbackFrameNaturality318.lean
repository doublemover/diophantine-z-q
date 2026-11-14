module
public import OriginalLineIsomPullbackUnits318
public import PullbackChartNaturality318
public section
noncomputable section
namespace OriginalChartPullbackFrameNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  {M N : Y.Modules} (a : M ≅ N)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
/-- Pullback of a complete original chart frame commutes with an actual
module isomorphism through the native chart NatIso, not a replacement
isomorphism selected only from equality of line classes. -/
lemma frame :
    LinePullbackFrames318.frame f N U (e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso a)=
      LinePullbackFrames318.frame f M U e ≪≫
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso ((Scheme.Modules.pullback f).mapIso a) := by
  apply Iso.ext
  let C := PullbackChartNaturality318.chartNatIso f U.ι (f ⁻¹ᵁ U).ι
    (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U)
  have h := C.inv.naturality a.hom
  change (Scheme.Modules.pullback (LinePullbackFrames318.chartMap f U)).map
      ((Scheme.Modules.restrictFunctor U.ι).map a.hom) ≫ C.inv.app N=
    C.inv.app M ≫ (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullback f).map a.hom) at h
  change (IdentityCotangent318.pullbackUnitIso (LinePullbackFrames318.chartMap f U)).inv ≫
    (Scheme.Modules.pullback (LinePullbackFrames318.chartMap f U)).map
      (e.hom ≫ (Scheme.Modules.restrictFunctor U.ι).map a.hom) ≫ C.inv.app N=_
  rw [Functor.map_comp,Category.assoc,h]
  simp only [Category.assoc]
end OriginalChartPullbackFrameNaturality318
