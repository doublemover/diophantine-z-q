module
public import RefinementDoubleCover318
public section
noncomputable section
namespace MixedOriginalDescentCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318 MixedCoverRecovery318
open ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  (D : Datum f)
abbrev arrow : mixed f g ⟶ Y := first f g ≫ f
lemma first_square : first f g ≫ f = arrow f g ≫ 𝟙 Y := (Category.comp_id _).symm
lemma second_square : second f g ≫ g = arrow f g ≫ 𝟙 Y := by
  rw [Category.comp_id]
  exact (square f g).symm
include factor in
lemma composite_square : (second f g ≫ a) ≫ f = arrow f g ≫ 𝟙 Y := by
  rw [Category.assoc,factor,second_square]

/-- The same mixed comparison preserves the original f-descent datum,
now tested over Y, rather than only the canonical mixed cover over X. -/
@[expose] def hom : Hom
    (OriginalSchemeDescentBaseChange318.datum f (arrow f g) (first f g) (𝟙 Y)
      (first_square f g) (OriginalCanonicalDescent318.datum f (baseLine f g a factor D)))
    (OriginalSchemeDescentBaseChange318.datum f (arrow f g) (first f g) (𝟙 Y)
      (first_square f g) D) :=
  (OriginalCanonicalDescent318.baseChange f (arrow f g) (first f g) (𝟙 Y)
    (first_square f g) (baseLine f g a factor D)).comp
  ((OriginalCanonicalDescent318.baseChangeInverse g (arrow f g) (second f g) (𝟙 Y)
    (second_square f g) (baseLine f g a factor D)).comp
  ((OriginalSchemeDescentBaseChangeMaps318.map (arrow f g) (second f g) (𝟙 Y) (second_square f g)
    (AffineMorphismGlobalEffectivity318.hom g (restricted f g a factor D))).comp
  ((OriginalDescentBaseChangePath318.hom f g (arrow f g) a (𝟙 Y)
    (by rw [factor,Category.comp_id]) (second f g) (𝟙 Y) (second_square f g)
    (second f g ≫ a) (𝟙 Y) (composite_square f g a factor) rfl (Category.comp_id _) D).comp
    (ActualDescentEvaluationChange318.hom D (arrow f g) (second f g ≫ a) (𝟙 Y)
      (composite_square f g a factor) (first f g) (first_square f g)))))

lemma square_comparisons (M : Y.Modules) :
    (coverComparison f (arrow f g) (first f g) (𝟙 Y) (first_square f g)).hom.app M ≫
      (coverComparison g (arrow f g) (second f g) (𝟙 Y) (second_square f g)).inv.app M =
    (coverComparison f (second f g) (first f g) g (square f g)).hom.app M := by
  have h₀ := PullbackSquareTarget318.cover_common f (arrow f g) (first f g) (𝟙 Y)
    (first_square f g) (arrow f g) rfl (Category.comp_id _)
  have h₁ := PullbackSquareTarget318.cover_common g (arrow f g) (second f g) (𝟙 Y)
    (second_square f g) (arrow f g) (square f g).symm (Category.comp_id _)
  have h₂ := PullbackSquareTarget318.cover_common f (second f g) (first f g) g
    (square f g) (arrow f g) rfl (square f g).symm
  apply (cancel_mono ((coverComparison g (arrow f g) (second f g) (𝟙 Y)
    (second_square f g)).hom.app M)).mp
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
  rw [h₀,h₁,h₂]
  simp only [NatTrans.comp_app,Category.assoc,Iso.inv_hom_id_app_assoc]

lemma hom_comparison : (hom f g a factor D).sheafHom = (comparison f g a factor D).hom := by
  simp only [hom,Hom.comp,OriginalCanonicalDescent318.baseChange,
    OriginalCanonicalDescent318.baseChangeInverse,OriginalCanonicalDescent318.inverse,
    OriginalSchemeDescentBaseChangeMaps318.map,OriginalDescentBaseChangePath318.hom,
    ActualDescentEvaluationChange318.hom,MixedCoverRecovery318.comparison,
    Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,
    ActualDescentTestEvaluation318.iso,Category.assoc]
  rw [← Category.assoc ((coverComparison f (arrow f g) (first f g) (𝟙 Y)
    (first_square f g)).hom.app (baseLine f g a factor D).object),square_comparisons] <;> rfl
end MixedOriginalDescentCompatibility318
