module
public import OriginalLineComparisonIdentity318
public import ScalarExtensionComposition318
public section
noncomputable section
namespace OriginalLineNamedComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : CommRingCat.{u}}

lemma ring_path {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
    (hh : g.hom.comp f.hom = h.hom) : f ≫ g = h := by
  ext r
  exact congrArg (fun k : R →+* T => k r) hh

/-- Canonical composition along a named ring path, including the actual
scheme equality transport dictated by its ring-map identity. -/
@[expose] def pullbackAlong (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (hh : g.hom.comp f.hom = h.hom) :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map h) :=
  AffineComparisonMates318.pullbackComp f g ≪≫
    Scheme.Modules.pullbackCongr (congrArg (fun k => Spec.map k) (ring_path hh))

lemma scalarCongr_refl (N : ModuleCat R) (f : R →+* S) :
    (ScalarExtensionCongr318.component (rfl : f = f) N).hom = 𝟙 _ := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  rfl

/-- The unchanged section comparison is coherent along each actual named
path. Equality transport on modules is precisely the existing tensor map. -/
lemma sections_composition (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (hh : g.hom.comp f.hom = h.hom) (L : Line (Spec R)) :
    (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom ≫
      (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      moduleSpecΓFunctor.map ((pullbackAlong f g h hh).hom.app L.object) =
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections R L) h.hom hh).hom ≫
      (sectionsIso h L).hom := by
  have hp := ring_path hh
  subst h
  simpa only [pullbackAlong, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    ScalarExtensionComposition318.comparison, Iso.symm_hom, NatIso.app_inv, scalarCongr_refl,
    Category.assoc] using OriginalLineComparisonComposition318.sections_composition f g L
end OriginalLineNamedComparison318
