module
public import ActualAffineBaseRefinement318
public section
noncomputable section
namespace AffineBaseFpqcDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 ActualAffineBaseRefinement318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Flat f] [Surjective f]
  [coverQC : QuasiCompactCover (cover f).toPreZeroHypercover]

/-- The refinement hypothesis is now discharged by the genuine finite
affine refinement of the original flat cover on the affine base. -/
@[expose] def equivalence : Line Y ≌ Datum f :=
  RefinedCoverCategoricalEquivalence318.equivalence f (refinement f).map
    (refinement f).lift (refinement f).factor

lemma functor_map {L K : Line Y} (h : L ⟶ K) :
    ((equivalence f).functor.map h).sheafHom = (Scheme.Modules.pullback f).map h := rfl

omit coverQC in
/-- Effective original descent for every flat quasi-compact covering
morphism onto an affine base, without assuming the source affine. -/
@[expose] def fpqcEquivalence [QuasiCompact f] : Line Y ≌ Datum f :=
  equivalence f
end AffineBaseFpqcDescent318
