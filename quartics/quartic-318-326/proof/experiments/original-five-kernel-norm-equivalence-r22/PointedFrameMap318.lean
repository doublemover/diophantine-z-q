module
public import UnitCocyclePointedLine318
public import PullbackScalar318
public section
noncomputable section
namespace PointedFrameMap318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) (U : Y.Opens)
    (em : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
    (en : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι)
/-- Exact local inverse-frame equation for a global map with a prescribed
original coefficient multiplier, using the unchanged open adjunction. -/
lemma local_equation (s : Γ(U.toScheme,⊤))
    (h : g ≫ LineFrameAdjunction318.coordinate N U en =
      LineFrameAdjunction318.coordinate M U em ≫
        (Scheme.Modules.pushforward U.ι).map (ClutchedModule318.multiply s)) :
    (Scheme.Modules.restrictFunctor U.ι).map g ≫ en.inv = em.inv ≫ ClutchedModule318.multiply s := by
  have hh := congrArg ((Scheme.Modules.restrictAdjunction U.ι).homEquiv M
    (SheafOfModules.unit U.toScheme.ringCatSheaf)).symm h
  rw [Adjunction.homEquiv_naturality_right_symm] at hh
  simpa only [Adjunction.homEquiv_naturality_left_symm, LineFrameAdjunction318.transpose] using hh
/-- Original chart-ring transport takes a reduction-one ambient coefficient to
one on the actual inverse-image chart. -/
lemma chart_scalar_one (a : Γ(Y,U)) (ha : f.app U a = 1) :
    (LinePullbackFrames318.chartMap f U).appTop (U.topIso.inv a) = 1 := by
  apply (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U).topIso.hom).1
  rw [map_one]
  have h := (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ f.appLE U (f ⁻¹ᵁ U) le_rfl =
    (LinePullbackFrames318.chartMap f U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom at h
  have hh := congrArg (fun k => k (U.topIso.inv a)) h
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, Scheme.Hom.appLE_eq_app] at hh
  exact hh.symm.trans ha
/-- An original chart scalar reducing to one makes the pulled original map
preserve the actual canonical pulled inverse frames. -/
lemma pulled_local_equation (s : Γ(U.toScheme,⊤))
    (h : (Scheme.Modules.restrictFunctor U.ι).map g ≫ en.inv =
      em.inv ≫ ClutchedModule318.multiply s)
    (hs : (LinePullbackFrames318.chartMap f U).appTop s = 1) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map g) ≫
      (LinePullbackFrames318.frame f N U en).inv =
        (LinePullbackFrames318.frame f M U em).inv := by
  rw [LinePullbackFrames318.inverse_formula, LinePullbackFrames318.inverse_formula]
  have hn := (PullbackChartNaturality318.chartNatIso f U.ι (f ⁻¹ᵁ U).ι
    (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U)).hom.naturality g
  change (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map g) ≫
    (PullbackLineFrames318.chartIso f U.ι (f ⁻¹ᵁ U).ι
      (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U) N).hom =
    (PullbackLineFrames318.chartIso f U.ι (f ⁻¹ᵁ U).ι
      (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U) M).hom ≫
      (Scheme.Modules.pullback (LinePullbackFrames318.chartMap f U)).map
        ((Scheme.Modules.restrictFunctor U.ι).map g) at hn
  simp only [← Category.assoc]
  rw [hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp]
  simp only [Category.assoc]
  rw [PullbackScalar318.pullback_multiply, hs, CocycleGaugeIso318.multiply_one, Category.comp_id]
/-- The exact global coordinate equation is recovered from the actual restricted
frame equation by the same original adjunction. -/
lemma pulled_coordinate (s : Γ(U.toScheme,⊤))
    (h : g ≫ LineFrameAdjunction318.coordinate N U en =
      LineFrameAdjunction318.coordinate M U em ≫
        (Scheme.Modules.pushforward U.ι).map (ClutchedModule318.multiply s))
    (hs : (LinePullbackFrames318.chartMap f U).appTop s = 1) :
    (Scheme.Modules.pullback f).map g ≫
      LineFrameAdjunction318.coordinate ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
        (LinePullbackFrames318.frame f N U en) =
      LineFrameAdjunction318.coordinate ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
        (LinePullbackFrames318.frame f M U em) := by
  apply ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, LineFrameAdjunction318.transpose,
    LineFrameAdjunction318.transpose]
  exact pulled_local_equation f g U em en s (local_equation g U em en s h) hs
end PointedFrameMap318
