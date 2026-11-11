module
public import PushforwardGlobalSections318
public import AffineDifferentialSheaf318
public section
noncomputable section
namespace CanonicalDifferentialSheafMap318
open CategoryTheory AlgebraicGeometry KaehlerDifferential
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

abbrev baseMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S T))
abbrev sourceSheaf := AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S)
abbrev targetSheaf := AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=T)
abbrev pushedSheaf := (Scheme.Modules.pushforward (baseMap (S:=S) (T:=T))).obj (targetSheaf (R:=R) (T:=T))

/-- The actual universal map with the precisely restricted scalar module structure. -/
@[expose] def differentialModuleMap : ModuleCat.of S (KaehlerDifferential R S) ⟶
    (ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T (KaehlerDifferential R T)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap S T)).obj
    (ModuleCat.of T (KaehlerDifferential R T))) {
    toFun := KaehlerDifferential.map R R S T
    map_add' := (KaehlerDifferential.map R R S T).map_add
    map_smul' := fun s ω => by
      change KaehlerDifferential.map R R S T (s • ω) =
        algebraMap S T s • KaehlerDifferential.map R R S T ω
      rw [map_smul,IsScalarTower.algebraMap_smul] }

/-- The actual universal differential map, read in the actual pushforward's global sections. -/
@[expose] def moduleToGlobal : ModuleCat.of S (KaehlerDifferential R S) ⟶
    moduleSpecΓFunctor.obj (pushedSheaf (R:=R) (S:=S) (T:=T)) :=
  differentialModuleMap ≫
    (ModuleCat.restrictScalars (algebraMap S T)).map
      (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom ≫
    (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap S T))
      (targetSheaf (R:=R) (T:=T))).inv

/-- The canonical actual sheaf morphism induced by the universal derivation,
    constructed by the genuine tilde/global-sections adjunction. -/
@[expose] def sheafMap : sourceSheaf (R:=R) (S:=S) ⟶
    pushedSheaf (R:=R) (S:=S) (T:=T) :=
  ((tilde.adjunction (R:=CommRingCat.of S)).homEquiv _ _).symm moduleToGlobal

theorem adjoint_sheafMap :
    (tilde.adjunction (R:=CommRingCat.of S)).homEquiv _ _
      (sheafMap (R:=R) (S:=S) (T:=T)) = moduleToGlobal :=
  Equiv.apply_symm_apply _ _

/-- Exact global-section normalization of the genuine sheaf map. -/
theorem global_normalization :
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ≫
      moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=S) (T:=T)) ≫
      (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap S T))
        (targetSheaf (R:=R) (T:=T))).hom =
    differentialModuleMap ≫
      (ModuleCat.restrictScalars (algebraMap S T)).map
        (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom := by
  have h:=adjoint_sheafMap (R:=R) (S:=S) (T:=T)
  rw [Adjunction.homEquiv_unit] at h
  change (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ≫
    moduleSpecΓFunctor.map sheafMap = moduleToGlobal at h
  rw [←Category.assoc,h,moduleToGlobal]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Every actual global universal differential is transported by the actual algebra map. -/
theorem global_image (ω : KaehlerDifferential R S) :
    (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap S T))
      (targetSheaf (R:=R) (T:=T))).hom
        ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=S) (T:=T)))
          ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω)) =
    (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom
      (KaehlerDifferential.map R R S T ω) := by
  have h:=congrArg (fun f => f ω) (global_normalization (R:=R) (S:=S) (T:=T))
  exact h

theorem global_image_D (s : S) :
    (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap S T))
      (targetSheaf (R:=R) (T:=T))).hom
        ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=S) (T:=T)))
          ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom (D R S s))) =
    (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom
      (D R T (algebraMap S T s)) := by
  rw [global_image,KaehlerDifferential.map_D]

/-- Uniqueness is a genuine sheaf-morphism assertion, not merely uniqueness of a formal coefficient. -/
theorem sheafMap_unique (g : sourceSheaf (R:=R) (S:=S) ⟶ pushedSheaf (R:=R) (S:=S) (T:=T))
    (hg : (tilde.adjunction (R:=CommRingCat.of S)).homEquiv _ _ g = moduleToGlobal) :
    g = sheafMap := by
  apply ((tilde.adjunction (R:=CommRingCat.of S)).homEquiv _ _).injective
  rw [hg,adjoint_sheafMap]

/-- On an actual open immersion, this canonical map gives a genuine restriction morphism. -/
@[expose] def restrictionMap [IsOpenImmersion (baseMap (S:=S) (T:=T))] :
    (Scheme.Modules.restrictFunctor (baseMap (S:=S) (T:=T))).obj (sourceSheaf (R:=R) (S:=S)) ⟶
      targetSheaf (R:=R) (T:=T) :=
  ((Scheme.Modules.restrictAdjunction (baseMap (S:=S) (T:=T))).homEquiv _ _).symm sheafMap

theorem adjoint_restrictionMap [IsOpenImmersion (baseMap (S:=S) (T:=T))] :
    (Scheme.Modules.restrictAdjunction (baseMap (S:=S) (T:=T))).homEquiv _ _
      (restrictionMap (R:=R) (S:=S) (T:=T)) = sheafMap :=
  Equiv.apply_symm_apply _ _
end CanonicalDifferentialSheafMap318
