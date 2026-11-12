module
public import TildePullback318
public section
noncomputable section
namespace AffineGlobalSectionCoherence318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : CommRingCat.{u}}

/-- The genuine affine pushforward comparison is identity on the underlying
section. Its source and target retain their different scalar actions. -/
lemma global_hom_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj M)) :
    (TildePullback318.globalNatIso f).hom.app M x = x := rfl

lemma global_inv_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (x : (ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj M)) :
    (TildePullback318.globalNatIso f).inv.app M x = x := rfl

/-- The actual comparison for the composite Spec map, with the equality of
scheme maps retained rather than silently replacing the original pullback. -/
@[expose] def specComp (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ≅
      Scheme.Modules.pushforward (Spec.map (f ≫ g)) :=
  Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
    Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm

/-- Composition on global sections agrees with actual successive restriction
of scalars. This is an equality of maps, not merely of isomorphism classes. -/
lemma composition (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules) :
    moduleSpecΓFunctor.map ((specComp f g).hom.app M) ≫
        (TildePullback318.globalNatIso (f ≫ g)).hom.app M ≫
        (ModuleCat.restrictScalarsComp f.hom g.hom).hom.app
          (moduleSpecΓFunctor.obj M) =
      (TildePullback318.globalNatIso f).hom.app
          ((Scheme.Modules.pushforward (Spec.map g)).obj M) ≫
        (ModuleCat.restrictScalars f.hom).map
          ((TildePullback318.globalNatIso g).hom.app M) := by
  apply ModuleCat.hom_ext
  ext x
  change M.presheaf.map (eqToHom (by rfl)).op x = x
  simp

/-- The inverse form needed to transpose the canonical composition square. -/
lemma inverse_composition (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules) :
    (ModuleCat.restrictScalarsComp f.hom g.hom).inv.app
        (moduleSpecΓFunctor.obj M) ≫
      (TildePullback318.globalNatIso (f ≫ g)).inv.app M =
    (ModuleCat.restrictScalars f.hom).map
        ((TildePullback318.globalNatIso g).inv.app M) ≫
      (TildePullback318.globalNatIso f).inv.app
        ((Scheme.Modules.pushforward (Spec.map g)).obj M) ≫
      moduleSpecΓFunctor.map ((specComp f g).hom.app M) := by
  let a := moduleSpecΓFunctor.mapIso ((specComp f g).app M)
  let b := (TildePullback318.globalNatIso (f ≫ g)).app M
  let c := (ModuleCat.restrictScalarsComp f.hom g.hom).app (moduleSpecΓFunctor.obj M)
  let d := (TildePullback318.globalNatIso f).app
    ((Scheme.Modules.pushforward (Spec.map g)).obj M)
  let e := (ModuleCat.restrictScalars f.hom).mapIso
    ((TildePullback318.globalNatIso g).app M)
  have h : a ≪≫ b ≪≫ c = d ≪≫ e := Iso.ext (composition f g M)
  have hi : c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
    simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv h
  change c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a.hom
  calc
    _ = (c.inv ≫ b.inv ≫ a.inv) ≫ a.hom := by simp only [Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    _ = (e.inv ≫ d.inv) ≫ a.hom := congrArg (fun k => k ≫ a.hom) hi
    _ = _ := Category.assoc _ _ _

/-- The genuine identity Spec map comparison. -/
@[expose] def specId (R : CommRingCat.{u}) :
    Scheme.Modules.pushforward (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules :=
  Scheme.Modules.pushforwardCongr (Spec.map_id R) ≪≫ Scheme.Modules.pushforwardId (Spec R)

lemma identity (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    moduleSpecΓFunctor.map ((specId R).hom.app M) =
      (TildePullback318.globalNatIso (𝟙 R)).hom.app M ≫
        (ModuleCat.restrictScalarsId R).hom.app (moduleSpecΓFunctor.obj M) := by
  apply ModuleCat.hom_ext
  ext x
  change M.presheaf.map (eqToHom (by rfl)).op x = x
  simp
end AffineGlobalSectionCoherence318
