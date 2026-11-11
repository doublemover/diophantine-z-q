module
public import OriginalSourceDescentTrivialization318
public section
noncomputable section
namespace MixedCoverCompatibleRecovery318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318 MixedCoverRecovery318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  (D : Datum f)

include factor in
lemma direct_square : (second f g ≫ a) ≫ f = first f g ≫ f :=
  (pair_condition f g a factor).symm

/-- The mixed recovery map is compatible with the genuine double of
the mixed cover. Its compatibility is assembled from original base-change
maps, the evaluated original triple law and the original diagonal law. -/
@[expose] def hom : Hom
    (OriginalCanonicalDescent318.datum (first f g)
      (LineSheafPullback318.line f (baseLine f g a factor D)))
    (OriginalCanonicalDescent318.datum (first f g) D.line) :=
  (OriginalCanonicalDescent318.baseChangeInverse g (first f g) (second f g) f
    (square f g).symm (baseLine f g a factor D)).comp
  ((OriginalSchemeDescentBaseChangeMaps318.map (first f g) (second f g) f (square f g).symm
    (AffineMorphismGlobalEffectivity318.hom g (restricted f g a factor D))).comp
  ((OriginalDescentBaseChangePath318.hom f g (first f g) a (𝟙 Y)
    (by rw [factor,Category.comp_id]) (second f g) f (square f g).symm
    (second f g ≫ a) f (direct_square f g a factor) rfl (Category.comp_id f) D).comp
  ((ActualDescentEvaluationChange318.hom D (first f g) (second f g ≫ a) f
    (direct_square f g a factor) (first f g) rfl).comp
    (OriginalSourceDescentTrivialization318.hom D (first f g)))))

lemma hom_comparison : (hom f g a factor D).sheafHom = (comparison f g a factor D).hom := by
  simp only [hom,Hom.comp,OriginalCanonicalDescent318.baseChangeInverse,
    OriginalCanonicalDescent318.inverse,OriginalSchemeDescentBaseChangeMaps318.map,
    OriginalDescentBaseChangePath318.hom,ActualDescentEvaluationChange318.hom,
    OriginalSourceDescentTrivialization318.hom,MixedCoverRecovery318.comparison,
    Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,
    ActualDescentTestEvaluation318.iso,Category.comp_id,Category.assoc]
  rw [PullbackSquareTarget318.cover_flip g (first f g) (second f g) f (square f g).symm] <;> rfl

/-- The reconstruction from the affine faithfully flat refinement is
isomorphic on the entire original covering scheme to the original line.
No affineness or flatness of the original arrow f is needed here. -/
@[expose] def recovery :
    (Scheme.Modules.pullback f).obj (baseLine f g a factor D).object ≅ D.line.object :=
  OriginalGlobalLineMapDescent318.iso (first f g) (comparison f g a factor D)
    (hom f g a factor D) (hom_comparison f g a factor D)

lemma recovery_cover : (Scheme.Modules.pullback (first f g)).mapIso (recovery f g a factor D) =
    comparison f g a factor D :=
  OriginalGlobalLineMapDescent318.iso_cover (first f g) (comparison f g a factor D)
    (hom f g a factor D) (hom_comparison f g a factor D)
end MixedCoverCompatibleRecovery318
