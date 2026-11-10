module
public import AffineOriginalCoverCompatibility318
public section
noncomputable section
namespace PullbackRestrictionCompatibility318
open AlgebraicGeometry CategoryTheory OpenSheafRestrictionCompatibility318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}

@[expose] def restriction (e : (Scheme.Modules.pullback U.ι).obj M ≅
    (Scheme.Modules.pullback U.ι).obj N) : M.restrict U.ι ≅ N.restrict U.ι :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm

/-- The proved original pullback-path square implies compatibility for
the original open-scheme restriction, with both endpoint comparisons. -/
lemma compatible (h : V ≤ U)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ (Scheme.Modules.pullback V.ι).obj N)
    (he : (Scheme.Modules.pullback (X.homOfLE h)).map eU.hom ≫
        (PullbackPathComposition318.iso (X.homOfLE h) U.ι V.ι (Scheme.homOfLE_ι X h)).hom.app N =
      (PullbackPathComposition318.iso (X.homOfLE h) U.ι V.ι (Scheme.homOfLE_ι X h)).hom.app M ≫ eV.hom) :
    schemeRestrict (restriction eU) h = restriction eV := by
  let R := Scheme.Modules.restrictFunctor (X.homOfLE h)
  let c := Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)
  let uM := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let uN := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N
  let vM := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M
  let vN := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N
  let q := PullbackPathComposition318.iso (X.homOfLE h) U.ι V.ι (Scheme.homOfLE_ι X h)
  have hpM := OpenRestrictionPathNormalization318.comparison_path M h
  have hpN := OpenRestrictionPathNormalization318.comparison_path N h
  change (path M h).hom ≫ R.map uM.hom ≫ c.hom.app _ ≫ q.hom.app M = vM.hom at hpM
  change (path N h).hom ≫ R.map uN.hom ≫ c.hom.app _ ≫ q.hom.app N = vN.hom at hpN
  have hpN' : (path N h).inv ≫ vN.hom =
      R.map uN.hom ≫ c.hom.app _ ≫ q.hom.app N := by
    rw [← hpN]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have hn := c.hom.naturality eU.hom
  apply Iso.ext
  apply (cancel_mono vN.hom).mp
  change ((path M h).hom ≫ R.map (uM.hom ≫ eU.hom ≫ uN.inv) ≫
    (path N h).inv) ≫ vN.hom = (vM.hom ≫ eV.hom ≫ vN.inv) ≫ vN.hom
  simp only [Functor.map_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [hpN']
  simp only [PullbackSquareTarget318.map_inv_hom_assoc]
  rw [← Category.assoc (R.map eU.hom),hn]
  simp only [Category.assoc]
  rw [he]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ eV.hom) hpM
end PullbackRestrictionCompatibility318
