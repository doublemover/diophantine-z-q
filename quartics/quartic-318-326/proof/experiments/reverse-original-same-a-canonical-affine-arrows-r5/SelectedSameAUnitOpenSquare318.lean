module

public import PullbackLocalRelations318
public import PullbackUnitComposition318
public import RestrictionPullbackCoherence318

/-!
# Canonical normalization of the unit factor on the actual open square

This removes the remaining unit ambiguity in restriction of a pulled
section. No étaleness or flatness of the vertical map is required.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace SelectedSameAUnitOpenSquare318

universe u
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

local notation "unit" => PulledCoordinateMaps318.unit
local notation "F" => Scheme.Modules.pullback
local notation "res" => Scheme.Modules.restrictFunctor
local notation "ul" => IdentityCotangent318.pullbackUnitIso
local notation "ur" => Scheme.Modules.restrictUnitIso
local notation "e" => Scheme.Modules.restrictFunctorIsoPullback

variable {X Y U V : Scheme.{u}}

private theorem unit_congr {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom.app (unit Y) ≫ (ul g).hom = (ul f).hom := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

variable (f : X ⟶ Y) (j : U ⟶ Y) (l : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion l] (r : V ⟶ U) (sq : l ≫ f = r ≫ j)

/-- The domain factor already occurring in the genuine square can have
no extra unit scaling: composing with the genuine pullback-of-unit map
recovers the actual restriction of the structure sheaf. -/
theorem domainFactor_normalized :
    PullbackLocalRelations318.domainFactor f j l r sq ≫ (ul r).hom = (ur l).hom := by
  let M := unit Y
  let cL := (Scheme.Modules.pullbackComp l f).hom.app M
  let cR := (Scheme.Modules.pullbackComp r j).inv.app M
  let eq := (Scheme.Modules.pullbackCongr sq).hom.app M
  have hj : (e j).inv.app M ≫ (ur j).hom = (ul j).hom := by
    have he := RestrictionPullbackCoherence318.restrict_unit j
    change (e j).hom.app M ≫ (ul j).hom = (ur j).hom at he
    calc
      _ = (e j).inv.app M ≫ (e j).hom.app M ≫ (ul j).hom := by rw [he]
      _ = _ := by
        rw [← Category.assoc]
        exact (congrArg (fun f => f ≫ (ul j).hom) ((e j).inv_hom_id_app M)).trans
          (Category.id_comp _)
  have hr : cR ≫ (F r).map ((ul j).hom) ≫ (ul r).hom = (ul (r ≫ j)).hom :=
    PullbackUnitComposition318.inverse_composition r j
  have hl : (F l).map ((ul f).inv) ≫ cL ≫ (ul (l ≫ f)).hom = (ul l).hom := by
    change (F l).map ((ul f).inv) ≫
      (Scheme.Modules.pullbackComp l f).hom.app (unit Y) ≫ (ul (l ≫ f)).hom = _
    rw [PullbackUnitComposition318.composition l f]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, (F l).map_id, Category.id_comp]
  have hc : (PullbackChartNaturality318.chartNatIso f j l r sq).hom.app M =
      (PullbackLineFrames318.chartIso f j l r sq M).hom :=
    congrArg Iso.hom (PullbackChartNaturality318.app_eq f j l r sq M)
  unfold PullbackLocalRelations318.domainFactor
  rw [hc]
  simp only [PullbackLineFrames318.chartIso, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  change (res l).map ((ul f).inv) ≫ (e l).hom.app ((F f).obj M) ≫
    cL ≫ eq ≫ cR ≫ (F r).map ((e j).inv.app M) ≫ (F r).map ((ur j).hom) ≫ (ul r).hom = _
  rw [← Functor.map_comp_assoc, hj, hr]
  change (res l).map ((ul f).inv) ≫ (e l).hom.app ((F f).obj M) ≫
    cL ≫ (Scheme.Modules.pullbackCongr sq).hom.app (unit Y) ≫ (ul (r ≫ j)).hom = _
  rw [unit_congr sq]
  rw [← Category.assoc ((res l).map _) ((e l).hom.app _) (cL ≫ (ul (l ≫ f)).hom)]
  rw [(e l).hom.naturality ((ul f).inv)]
  simp only [Category.assoc]
  rw [hl, RestrictionPullbackCoherence318.restrict_unit l]

/-- Restriction of a genuine pulled section is the genuine pullback of its
restriction after comparison with the literal structure sheaf on the chart. -/
theorem restrict_pulled_section {L : Y.Modules} (s : unit Y ⟶ L) :
    (ur l).inv ≫ (res l).map (PulledCoordinateMaps318.map f s) ≫
        (PullbackChartNaturality318.chartNatIso f j l r sq).hom.app L =
      PulledCoordinateMaps318.map r (LocalCoordinateRelation318.localMap j s) := by
  have hh : (ur l).inv ≫ PullbackLocalRelations318.domainFactor f j l r sq =
      (ul r).inv := by
    apply (cancel_mono (ul r).hom).mp
    simp only [Category.assoc, domainFactor_normalized f j l r sq, Iso.inv_hom_id]
  rw [PullbackLocalRelations318.factorization f j l r sq s]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc, hh] <;> rfl

end SelectedSameAUnitOpenSquare318
