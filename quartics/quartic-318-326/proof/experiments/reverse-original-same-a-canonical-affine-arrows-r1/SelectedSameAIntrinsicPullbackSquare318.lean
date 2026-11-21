module

public import IntrinsicDifferentialFunctor318
public import FamilyRestrictionNormalization318
public import PullbackLineFrames318
public import RestrictionPullbackCoherence318

/-!
# The actual intrinsic differential arrow on a genuine open square

This proves compatibility of morphisms, not just of their source modules.
The relative map f and its within-chart map r need not be flat.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace SelectedSameAIntrinsicPullbackSquare318

universe u
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

local notation "F" => Scheme.Modules.pullback
local notation "G" => Scheme.Modules.pushforward
local notation "adj" => Scheme.Modules.pullbackPushforwardAdjunction
local notation "PB" => IntrinsicDifferentialPullback318.pullbackMap
local notation "PD" => IntrinsicDifferentialPullback318.map
local notation "Ω" => FamilyIntrinsicDifferentials318.omega

variable {X Y Z V U : Scheme.{u}} {R : CommRingCat.{u}}

private theorem adjoint_comp_mate (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {N : X.Modules}
    (m : (F f).obj ((F g).obj M) ⟶ N) :
    (adj (f ≫ g)).homEquiv _ _ ((Scheme.Modules.pullbackComp f g).inv.app M ≫ m) =
      ((adj g).comp (adj f)).homEquiv _ _ m ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  rw [PullbackUnitComposition318.homEquiv_mate ((adj g).comp (adj f))
    (adj (f ≫ g)), Scheme.Modules.conjugateEquiv_pullbackComp_inv]

/-- Compose the intrinsic pullback arrows via the exact selected
pseudofunctor comparison, with no assumptions on f or g. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (t : Z ⟶ Spec R)
    (hf : f ≫ q = p) (hg : g ≫ t = q) (hfg : (f ≫ g) ≫ t = p) :
    (Scheme.Modules.pullbackComp f g).inv.app (Ω t) ≫
        (F f).map (PB g q t hg) ≫ PB f p q hf =
      PB (f ≫ g) p t hfg := by
  apply ((adj (f ≫ g)).homEquiv _ _).injective
  rw [adjoint_comp_mate f g, Adjunction.comp_homEquiv]
  change (adj g).homEquiv _ _
      ((adj f).homEquiv _ _ ((F f).map (PB g q t hg) ≫ PB f p q hf)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (Ω p) =
    (adj (f ≫ g)).homEquiv _ _ (PB (f ≫ g) p t hfg)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    IntrinsicDifferentialPullback318.pullbackMap_adjoint,
    IntrinsicDifferentialPullback318.pullbackMap_adjoint,
    IntrinsicDifferentialPullback318.pullbackMap_adjoint]
  exact (IntrinsicDifferentialFunctor318.map_comp f g p q t hf hg hfg).symm

/-- On an actual open immersion, the chosen restriction comparison of
intrinsic differentials is exactly the adjoint differential map. -/
theorem open_normalized (j : U ⟶ Y) [IsOpenImmersion j] (q : Y ⟶ Spec R) :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (Ω q) ≫
        PB j (j ≫ q) q rfl =
      (FamilyRestrictionNormalization318.iso j q).hom := by
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).injective
  rw [RestrictionPullbackCoherence318.adjoint_restrict,
    IntrinsicDifferentialPullback318.pullbackMap_adjoint]
  apply UniversalSheafDifferentials318.hom_ext (FamilyIntrinsicDifferentials318.coefficients q)
  ext W s
  rw [IntrinsicDifferentialPullback318.map_D, FamilyRestrictionNormalization318.adjoint_D]

private theorem pullback_congr {f g : X ⟶ Y} (e : f = g)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (hf : f ≫ q = p) (hg : g ≫ q = p) :
    (Scheme.Modules.pullbackCongr e).hom.app (Ω q) ≫ PB g p q hg = PB f p q hf := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

private theorem pullback_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (t : Z ⟶ Spec R)
    (hf : f ≫ q = p) (hg : g ≫ t = q) (hfg : (f ≫ g) ≫ t = p) :
    (Scheme.Modules.pullbackComp f g).hom.app (Ω t) ≫ PB (f ≫ g) p t hfg =
      (F f).map (PB g q t hg) ≫ PB f p q hf := by
  rw [← pullback_comp f g p q t hf hg hfg, ← Category.assoc]
  simp only [Iso.hom_inv_id_app, Category.id_comp]

/-- Restrict the real ambient map to the given open square. The right side
uses precisely the intrinsic differential arrow of the given chart map r. -/
theorem actual_open_square (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (hf : f ≫ q = p) (j : U ⟶ Y) (l : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion l] (r : V ⟶ U) (sq : l ≫ f = r ≫ j) :
    (Scheme.Modules.restrictFunctor l).map (PB f p q hf) ≫
      (FamilyRestrictionNormalization318.iso l p).hom =
    (PullbackLineFrames318.chartIso f j l r sq (Ω q)).hom ≫
      (F r).map (FamilyRestrictionNormalization318.iso j q).hom ≫
      PB r (l ≫ p) (j ≫ q) (by rw [← Category.assoc, ← sq, Category.assoc, hf]) := by
  let hl : (l ≫ f) ≫ q = l ≫ p := by rw [Category.assoc, hf]
  let hr : r ≫ (j ≫ q) = l ≫ p := by rw [← Category.assoc, ← sq, Category.assoc, hf]
  let hcomp : (r ≫ j) ≫ q = l ≫ p := by rw [← sq]; exact hl
  let il := (Scheme.Modules.restrictFunctorIsoPullback l).hom.app ((F f).obj (Ω q))
  let ij := (Scheme.Modules.restrictFunctorIsoPullback j).app (Ω q)
  have hleft :
      (Scheme.Modules.restrictFunctor l).map (PB f p q hf) ≫
          (FamilyRestrictionNormalization318.iso l p).hom =
        il ≫ (Scheme.Modules.pullbackComp l f).hom.app (Ω q) ≫
          PB (l ≫ f) (l ≫ p) q hl := by
    rw [← open_normalized l p, ← Category.assoc]
    rw [(Scheme.Modules.restrictFunctorIsoPullback l).hom.naturality
      (PB f p q hf), Category.assoc]
    rw [pullback_comp_hom l f (l ≫ p) p q rfl hf hl] <;> rfl
  have hj : ij.inv ≫ (FamilyRestrictionNormalization318.iso j q).hom =
      PB j (j ≫ q) q rfl := by
    rw [← open_normalized j q, ← Category.assoc]
    simp only [ij, Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app, Category.id_comp]
  have hright :
      (Scheme.Modules.pullbackComp r j).inv.app (Ω q) ≫
        (F r).map ij.inv ≫ (F r).map (FamilyRestrictionNormalization318.iso j q).hom ≫
        PB r (l ≫ p) (j ≫ q) hr =
      PB (r ≫ j) (l ≫ p) q hcomp := by
    rw [← Functor.map_comp_assoc, hj]
    exact pullback_comp r j (l ≫ p) (j ≫ q) q hr rfl hcomp
  rw [hleft]
  change _ = _ ≫ (F r).map (FamilyRestrictionNormalization318.iso j q).hom ≫
    PB r (l ≫ p) (j ≫ q) hr
  simp only [PullbackLineFrames318.chartIso, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  change _ = il ≫ (Scheme.Modules.pullbackComp l f).hom.app (Ω q) ≫
    (Scheme.Modules.pullbackCongr sq).hom.app (Ω q) ≫
    (Scheme.Modules.pullbackComp r j).inv.app (Ω q) ≫
    (F r).map ij.inv ≫ (F r).map (FamilyRestrictionNormalization318.iso j q).hom ≫
    PB r (l ≫ p) (j ≫ q) hr
  rw [hright, pullback_congr sq (l ≫ p) q hl hcomp]

/-- Rebase the same proof along the two actual structural triangles, not
via independently chosen sheaf equivalences. -/
theorem actual_open_square_rebased (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (hf : f ≫ q = p) (j : U ⟶ Y) (l : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion l] (r : V ⟶ U) (sq : l ≫ f = r ≫ j)
    (u : U ⟶ Spec R) (v : V ⟶ Spec R)
    (hj : j ≫ q = u) (hl : l ≫ p = v) (hr : r ≫ u = v) :
    let du : FamilyRestrictionNormalization318.Data j
        (FamilyIntrinsicDifferentials318.coefficients q)
        (FamilyIntrinsicDifferentials318.coefficients u) :=
      congrArg FamilyIntrinsicDifferentials318.coefficients hj ▸
        FamilyRestrictionNormalization318.familyData j q
    let dv : FamilyRestrictionNormalization318.Data l
        (FamilyIntrinsicDifferentials318.coefficients p)
        (FamilyIntrinsicDifferentials318.coefficients v) :=
      congrArg FamilyIntrinsicDifferentials318.coefficients hl ▸
        FamilyRestrictionNormalization318.familyData l p
    (Scheme.Modules.restrictFunctor l).map (PB f p q hf) ≫ dv.iso.hom =
      (PullbackLineFrames318.chartIso f j l r sq (Ω q)).hom ≫
        (F r).map du.iso.hom ≫ PB r v u hr := by
  subst u
  subst v
  exact actual_open_square f p q hf j l r sq

end SelectedSameAIntrinsicPullbackSquare318
