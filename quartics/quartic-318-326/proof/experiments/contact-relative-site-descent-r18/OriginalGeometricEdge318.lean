module
public import AffineSectionConjugation318
public section
noncomputable section
namespace OriginalGeometricEdge318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
open OriginalLineNamedComparison318
set_option maxHeartbeats 1000000
set_option profiler true
set_option profiler.threshold 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- Normalize only the sheaf-object projection. Unfolding the whole line
record also expands all transported frames and cover proofs inside the
large categorical equality; those fields are irrelevant to this square. -/
private lemma pulled_object {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line Y) :
    (LineSheafPullback318.line f L).object = (Scheme.Modules.pullback f).obj L.object := rfl

variable {R S T : CommRingCat.{u}} (L : Line (Spec R))
  (f g : R ⟶ S) (m : S ⟶ T) (v w : R ⟶ T)
  (hv : m.hom.comp f.hom = v.hom) (hw : m.hom.comp g.hom = w.hom)
  (h : (LineSheafPullback318.line (Spec.map f) L).object ⟶
    (LineSheafPullback318.line (Spec.map g) L).object)

/-- Normalize the genuine sheaf pullback of an overlap morphism using
actual sheaf pullback composition and actual named Spec path equalities. -/
@[expose] def edge :
    (LineSheafPullback318.line (Spec.map v) L).object ⟶
      (LineSheafPullback318.line (Spec.map w) L).object :=
  (pullbackAlong f m v hv).inv.app L.object ≫
    (Scheme.Modules.pullback (Spec.map m)).map h ≫
    (pullbackAlong g m w hw).hom.app L.object

/-- Name the original composite comparison once, leaving its geometric
line certificate behind an opaque comparison interface. -/
private def endpoint (f : R ⟶ S) (m : S ⟶ T) :=
  (ModuleCat.extendScalars m.hom).mapIso (sectionsIso f L) ≪≫
    sectionsIso m (LineSheafPullback318.line (Spec.map f) L)

private lemma endpoint_square (f : R ⟶ S) (m : S ⟶ T) (v : R ⟶ T)
    (hv : m.hom.comp f.hom = v.hom) :
    (ScalarExtensionComposition318.comparison f.hom m.hom
      (OriginalLineAffineModel318.sections R L) v.hom hv).hom ≫ (sectionsIso v L).hom =
    (endpoint L f m).hom ≫ moduleSpecΓFunctor.map ((pullbackAlong f m v hv).app L.object).hom := by
  simpa only [endpoint,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,pulled_object,Category.assoc]
    using (sections_composition f m v hv L).symm

/-- Global sections of the actual geometric normalized edge equal the
actual scalar normalized edge. This is derived from original comparison
coherence and morphism naturality, not imposed as a hypothesis. -/
lemma edge_to_module :
    AffineSectionConjugation318.morphism L v w (edge L f g m v w hv hw h) =
      (ScalarExtensionComposition318.comparison f.hom m.hom
        (OriginalLineAffineModel318.sections R L) v.hom hv).inv ≫
      (ModuleCat.extendScalars m.hom).map (AffineSectionConjugation318.morphism L f g h) ≫
      (ScalarExtensionComposition318.comparison g.hom m.hom
        (OriginalLineAffineModel318.sections R L) w.hom hw).hom :=
  AffineSectionConjugation318.normalized_map moduleSpecΓFunctor
    (endpoint L f m) (endpoint L g m) (sectionsIso v L) (sectionsIso w L)
    ((pullbackAlong f m v hv).app L.object) ((pullbackAlong g m w hw).app L.object)
    (ScalarExtensionComposition318.comparison f.hom m.hom
      (OriginalLineAffineModel318.sections R L) v.hom hv)
    (ScalarExtensionComposition318.comparison g.hom m.hom
      (OriginalLineAffineModel318.sections R L) w.hom hw)
    (endpoint_square L f m v hv) (endpoint_square L g m w hw)
    ((Scheme.Modules.pullback (Spec.map m)).map h)
    ((ModuleCat.extendScalars m.hom).map (AffineSectionConjugation318.morphism L f g h))
    (AffineSectionConjugation318.pulled_morphism L f g m h)
end OriginalGeometricEdge318
