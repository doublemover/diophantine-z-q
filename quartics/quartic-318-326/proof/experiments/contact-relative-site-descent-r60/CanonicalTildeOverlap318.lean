module
public import CanonicalScalarOverlap318
public section
noncomputable section
namespace CanonicalTildeOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineAffineBaseChange318 OriginalLineNamedComparison318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

@[expose] def stepIso {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (M : ModuleCat R) :
    tilde ((ModuleCat.extendScalars g.hom).obj ((ModuleCat.extendScalars f.hom).obj M)) ≅
      (Scheme.Modules.pullback (Spec.map g)).obj ((Scheme.Modules.pullback (Spec.map f)).obj (tilde M)) :=
  ((TildePullback318.pullbackIso g).app ((ModuleCat.extendScalars f.hom).obj M)).symm ≪≫
    (Scheme.Modules.pullback (Spec.map g)).mapIso ((TildePullback318.pullbackIso f).app M).symm

lemma named_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (hh : g.hom.comp f.hom = h.hom) (M : ModuleCat R) :
    stepIso f g M ≪≫ (pullbackAlong f g h hh).app (tilde M) =
      (tilde.functor T).mapIso (ScalarExtensionComposition318.comparison f.hom g.hom M h.hom hh) ≪≫
        ((TildePullback318.pullbackIso h).app M).symm := by
  have hp := ring_path hh
  subst h
  apply Iso.ext
  simpa only [stepIso, pullbackAlong, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    ScalarExtensionComposition318.comparison, scalarCongr_refl, Category.assoc,
    Functor.comp_obj, tilde.functor_obj] using
      TildePullbackInverseComposition318.composition f g M

@[expose] def coverComparison {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat R)
    (L : Line (Spec S)) (e : (ModuleCat.extendScalars f.hom).obj M ≅ OriginalLineAffineModel318.sections S L) :
    (Scheme.Modules.pullback (Spec.map f)).obj (tilde M) ≅ L.object :=
  (TildePullback318.pullbackIso f).app M ≪≫ (tilde.functor S).mapIso e ≪≫
    OriginalLineAffineModel318.canonicalIso S L

/-- The original specified module comparison induces exactly the original
endpoint square for the displayed sheaf reconstruction comparison. -/
lemma endpoint {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (M : ModuleCat R)
    (L : Line (Spec S)) (e : (ModuleCat.extendScalars f.hom).obj M ≅ OriginalLineAffineModel318.sections S L) :
    (tilde.functor T).map ((ModuleCat.extendScalars g.hom).map e.hom) ≫ (sheafIso g L).hom =
      (stepIso f g M).hom ≫
        (Scheme.Modules.pullback (Spec.map g)).map (coverComparison f M L e).hom := by
  let P := Scheme.Modules.pullback (Spec.map g)
  have hn := (TildePullback318.pullbackIso g).inv.naturality e.hom
  have h := congrArg (fun k => k ≫ P.map L.object.fromTildeΓ) hn
  have hc : P.map ((TildePullback318.pullbackIso f).inv.app M) ≫
      P.map ((TildePullback318.pullbackIso f).hom.app M)=𝟙 _ := by
    simpa only [Functor.map_comp,Functor.map_id] using
      congrArg (fun k => P.map k) ((TildePullback318.pullbackIso f).inv_hom_id_app M)
  have hr : (stepIso f g M).hom ≫ P.map (coverComparison f M L e).hom =
      (TildePullback318.pullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
        P.map ((tilde.functor S).map e.hom) ≫ P.map L.object.fromTildeΓ := by
    simp only [stepIso, coverComparison, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      OriginalLineAffineModel318.canonicalIso_hom]
    change (TildePullback318.pullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
      P.map ((TildePullback318.pullbackIso f).inv.app M) ≫
      P.map (((TildePullback318.pullbackIso f).hom.app M ≫ (tilde.functor S).map e.hom) ≫
        L.object.fromTildeΓ)=_
    rw [P.map_comp,P.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (P.map ((TildePullback318.pullbackIso f).inv.app M)),hc,Category.id_comp]
  rw [hr]
  simpa only [sheafIso_counit, Functor.comp_map, Category.assoc] using h

variable (R S : CommRingCat.{u}) [Algebra R S] (M : ModuleCat R)
open AffineModuleBaseChange318 CanonicalScalarOverlap318
abbrev ringMap : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
abbrev leftPath := (pullbackAlong (ringMap R S) (leftMap R S S) (base R S) (left_path R S)).app (tilde M)
abbrev rightPath := (pullbackAlong (ringMap R S) (rightMap R S S) (base R S) (right_path R S)).app (tilde M)

/-- Canonical overlap of the actual pullback of a base tilde sheaf. -/
@[expose] def sheafOverlap :
    (Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj
      ((Scheme.Modules.pullback (Spec.map (ringMap R S))).obj (tilde M)) ⟶
    (Scheme.Modules.pullback (Spec.map (rightMap R S S))).obj
      ((Scheme.Modules.pullback (Spec.map (ringMap R S))).obj (tilde M)) :=
  (leftPath R S M).hom ≫ (rightPath R S M).inv

lemma canonical_square :
    (stepIso (ringMap R S) (leftMap R S S) M).hom ≫ sheafOverlap R S M =
      (tilde.functor (ring R S S)).map (CanonicalScalarOverlap318.overlap R S M) ≫
        (stepIso (ringMap R S) (rightMap R S S) M).hom := by
  have hl := congrArg Iso.hom (named_composition (ringMap R S) (leftMap R S S)
    (base R S) (left_path R S) M)
  have hr := congrArg Iso.hom (named_composition (ringMap R S) (rightMap R S S)
    (base R S) (right_path R S) M)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom] at hl hr
  apply (cancel_mono (rightPath R S M).hom).mp
  simp only [sheafOverlap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (stepIso (ringMap R S) (leftMap R S S) M).hom ≫
      (pullbackAlong (ringMap R S) (leftMap R S S) (base R S) (left_path R S)).hom.app (tilde M)=
    (tilde.functor (ring R S S)).map (CanonicalScalarOverlap318.overlap R S M) ≫
      (stepIso (ringMap R S) (rightMap R S S) M).hom ≫
      (pullbackAlong (ringMap R S) (rightMap R S S) (base R S) (right_path R S)).hom.app (tilde M)
  simp only [Functor.comp_obj,tilde.functor_obj] at hl hr ⊢
  rw [hl, hr]
  simp only [CanonicalScalarOverlap318.overlap, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

lemma canonical_conjugation :
    (stepIso (ringMap R S) (leftMap R S S) M).hom ≫ sheafOverlap R S M ≫
      (stepIso (ringMap R S) (rightMap R S S) M).inv =
        (tilde.functor (ring R S S)).map (CanonicalScalarOverlap318.overlap R S M) := by
  have h := congrArg (fun k => k ≫ (stepIso (ringMap R S) (rightMap R S S) M).inv)
    (canonical_square R S M)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
end CanonicalTildeOverlap318
