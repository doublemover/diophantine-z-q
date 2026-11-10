module
public import OriginalDoubleCoverFaithful318
public section
noncomputable section
namespace OriginalCanonicalDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U : Scheme.{u}} (f : U ⟶ B)

/-- Canonical actual-double descent data of every original base line. -/
@[expose] def datum (L : Line B) : Datum f where
  line := LineSheafPullback318.line f L
  overlap := CanonicalSheafOverlap318.actual L.object f
  diagonal := CanonicalActualDescentLaws318.diagonal_identity L.object f (𝟙 U) rfl
  triple := CanonicalActualDescentLaws318.triple L.object f

@[expose] def map {L K : Line B} (h : L.object ⟶ K.object) : Hom (datum f L) (datum f K) where
  sheafHom := (Scheme.Modules.pullback f).map h
  commutes := CanonicalActualDescentFunctor318.overlap_natural f h (first f) (second f)
    (first f ≫ f) rfl (edge_condition f).symm

/-- The inverse of a specified compatible original isomorphism is
compatible with the same original double maps. -/
@[expose] def inverse {D E : Datum f} (e : D.line.object ≅ E.line.object)
    (h : D.overlap ≫ (Scheme.Modules.pullback (second f)).map e.hom =
      (Scheme.Modules.pullback (first f)).map e.hom ≫ E.overlap) : Hom E D where
  sheafHom := e.inv
  commutes := by
    let a := (Scheme.Modules.pullback (first f)).mapIso e
    let b := (Scheme.Modules.pullback (second f)).mapIso e
    change E.overlap ≫ b.inv = a.inv ≫ D.overlap
    apply (cancel_epi a.hom).mp
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Iso.hom_inv_id_assoc]
    exact h.symm

variable {B' U' : Scheme.{u}} (g : U' ⟶ B') (a : U' ⟶ U) (b : B' ⟶ B)
  (square : a ≫ f = g ≫ b) (L : Line B)

@[expose] def baseChange : Hom
    (OriginalSchemeDescentBaseChange318.datum f g a b square (datum f L))
    (datum g (LineSheafPullback318.line b L)) where
  sheafHom := (coverComparison f g a b square).hom.app L.object
  commutes := CanonicalDescentBaseChange318.overlap_square f g a b square L.object

@[expose] def baseChangeInverse : Hom
    (datum g (LineSheafPullback318.line b L))
    (OriginalSchemeDescentBaseChange318.datum f g a b square (datum f L)) :=
  inverse g ((coverComparison f g a b square).app L.object) (baseChange f g a b square L).commutes
end OriginalCanonicalDescent318
