module
public import AffineCoalgebraModule318
public import FaithfullyFlatLineModule318
public import AffineRankOneLine318
public import TildePullback318
public import ScalarExtensionTensor318
public import LineSheafPullback318
public section
noncomputable section
namespace AffineCoalgebraLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
abbrev ringMap : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
lemma faithfullyFlat : (ringMap R S).hom.FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
variable (D : AffineCoalgebraModule318.Data (ringMap R S).hom)
  (L : Line (Spec S)) (e : D.A ≅ OriginalLineAffineModel318.sections S L)
abbrev baseModule := AffineCoalgebraModule318.descended (ringMap R S).hom
  (faithfullyFlat R S) D

@[expose] def scalarIso : (ModuleCat.extendScalars (ringMap R S).hom).obj (baseModule R S D) ≅
    OriginalLineAffineModel318.sections S L :=
  AffineCoalgebraModule318.moduleIso (ringMap R S).hom (faithfullyFlat R S) D ≪≫ e

include e in
lemma properties : Module.FinitePresentation R (baseModule R S D) ∧
    Module.Flat R (baseModule R S D) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (baseModule R S D) p = 1 :=
  FaithfullyFlatLineModule318.properties R S (baseModule R S D) L
    ((ScalarExtensionTensor318.tensorEquiv (S := R) (T := S) (baseModule R S D)).symm.trans
      (scalarIso R S D L e).toLinearEquiv)

/-- A genuine scalar-extension coalgebra whose covering module is the
actual section module of an original line descends to an actual line on
the original affine base, with full principal-open frames. -/
@[expose] def line : Line (Spec R) := by
  let := (properties R S D L e).1
  let := (properties R S D L e).2.1
  exact AffineRankOneLine318.line R (baseModule R S D) (properties R S D L e).2.2

lemma line_object : (line R S D L e).object = tilde (baseModule R S D) := rfl

/-- Its original sheaf pullback is the unchanged input line. The exact
comparison uses the original canonical tilde pullback and tilde-Gamma
counit, rather than only equality of module ranks or abstract classes. -/
@[expose] def pullbackIso :
    (LineSheafPullback318.line (Spec.map (ringMap R S)) (line R S D L e)).object ≅ L.object :=
  (TildePullback318.pullbackIso (ringMap R S)).app (baseModule R S D) ≪≫
    (tilde.functor S).mapIso (scalarIso R S D L e) ≪≫
    OriginalLineAffineModel318.canonicalIso S L

lemma pullbackIso_hom : (pullbackIso R S D L e).hom =
    ((TildePullback318.pullbackIso (ringMap R S)).app (baseModule R S D)).hom ≫
      (tilde.functor S).map (scalarIso R S D L e).hom ≫ L.object.fromTildeΓ := rfl
end AffineCoalgebraLine318
