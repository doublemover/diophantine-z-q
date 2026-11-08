module
public import PullbackLineFrames318
public section
noncomputable section
namespace PullbackChartNaturality318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y U V : Scheme.{u}} (p : X ⟶ Y)
    (j : U ⟶ Y) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (g : V ⟶ U) (h : k≫p=g≫j)
/-- The full natural change-of-chart isomorphism for actual inverse-image modules. -/
@[expose] def chartNatIso :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.restrictFunctor k ≅
      Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback p) (Scheme.Modules.restrictFunctorIsoPullback k) ≪≫
    Scheme.Modules.pullbackComp k p ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g j).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm (Scheme.Modules.pullback g)

theorem app_eq (L : Y.Modules) : (chartNatIso p j k g h).app L=
    PullbackLineFrames318.chartIso p j k g h L := rfl

include g h in
/-- Pulling back a chartwise isomorphism retains the actual restricted morphism,
not only an abstract isomorphic object. -/
theorem restricted_map_isIso {M N : Y.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor j).map f)] :
    IsIso ((Scheme.Modules.restrictFunctor k).map ((Scheme.Modules.pullback p).map f)) := by
  have hh := (chartNatIso p j k g h).hom.naturality f
  simp only [Functor.comp_map] at hh
  have he : (Scheme.Modules.restrictFunctor k).map ((Scheme.Modules.pullback p).map f)=
      (chartNatIso p j k g h).hom.app M ≫
      (Scheme.Modules.pullback g).map ((Scheme.Modules.restrictFunctor j).map f) ≫
      (chartNatIso p j k g h).inv.app N := by
    calc
      _ = ((Scheme.Modules.restrictFunctor k).map ((Scheme.Modules.pullback p).map f) ≫
          (chartNatIso p j k g h).hom.app N) ≫ (chartNatIso p j k g h).inv.app N := by simp
      _ = _ := by rw [hh]; simp only [Category.assoc]
  rw [he]
  infer_instance
end PullbackChartNaturality318
