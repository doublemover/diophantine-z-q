module
public import ActualTwoDescentIdealLocalizationAdjoint318
public section
noncomputable section
namespace ActualTwoDescentCanonicalIdealLocalizationMap318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentIdealLocalizationAdjoint318
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S] (I : Ideal R)
abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap R S))
abbrev sourceSheaf := tilde (R:=CommRingCat.of R) (ModuleCat.of R I)
abbrev targetSheaf := tilde (R:=CommRingCat.of S) (ModuleCat.of S (I.map (algebraMap R S)))
abbrev pushedSheaf := (Scheme.Modules.pushforward (baseMap S)).obj (targetSheaf S I)

def moduleToGlobal : ModuleCat.of R I ⟶ moduleSpecΓFunctor.obj (pushedSheaf S I) :=
  idealModuleMap S I ≫ (ModuleCat.restrictScalars (algebraMap R S)).map
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (I.map (algebraMap R S)))).hom ≫
      (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap R S))
        (targetSheaf S I)).inv

def sheafMap : sourceSheaf I ⟶ pushedSheaf S I :=
  ((tilde.adjunction (R:=CommRingCat.of R)).homEquiv _ _).symm (moduleToGlobal S I)

lemma adjoint_sheafMap : (tilde.adjunction (R:=CommRingCat.of R)).homEquiv _ _
    (sheafMap S I)=moduleToGlobal S I := Equiv.apply_symm_apply _ _

/-- Complete global-section normalization of the ACTUAL sheaf map. -/
lemma global_normalization :
    (tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R I)).hom ≫
      moduleSpecΓFunctor.map (sheafMap S I) ≫
        (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap R S))
          (targetSheaf S I)).hom =
    idealModuleMap S I ≫ (ModuleCat.restrictScalars (algebraMap R S)).map
      (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (I.map (algebraMap R S)))).hom := by
  have h := adjoint_sheafMap S I
  rw [Adjunction.homEquiv_unit] at h
  change (tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R I)).hom ≫
    moduleSpecΓFunctor.map (sheafMap S I)=moduleToGlobal S I at h
  rw [←Category.assoc,h,moduleToGlobal]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma global_image (x : I) :
    (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap R S))
      (targetSheaf S I)).hom
      ((moduleSpecΓFunctor.map (sheafMap S I))
        ((tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R I)).hom x)) =
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (I.map (algebraMap R S)))).hom
      (idealModuleMap S I x) :=
  congrArg (fun f => f x) (global_normalization S I)

variable [IsOpenImmersion (baseMap S)]
def restrictionMap : (sourceSheaf I).restrict (baseMap S) ⟶ targetSheaf S I :=
  ((Scheme.Modules.restrictAdjunction (baseMap S)).homEquiv _ _).symm (sheafMap S I)
lemma adjoint_restrictionMap : (Scheme.Modules.restrictAdjunction (baseMap S)).homEquiv _ _
    (restrictionMap S I)=sheafMap S I := Equiv.apply_symm_apply _ _
end ActualTwoDescentCanonicalIdealLocalizationMap318
