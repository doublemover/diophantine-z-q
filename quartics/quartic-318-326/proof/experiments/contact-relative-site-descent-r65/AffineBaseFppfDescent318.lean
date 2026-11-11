module
public import AffineBaseFpqcDescent318
public section
noncomputable section
namespace AffineBaseFppfDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 ActualAffineBaseRefinement318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Flat f] [Surjective f]
  [LocallyOfFinitePresentation f]

/-- Flat locally finitely presented maps are open, which gives the
actual quasi-compact-cover condition needed for finite affine refinement.
The original morphism need not itself be quasi-compact. -/
lemma cover_quasiCompact : QuasiCompactCover (cover f).toPreZeroHypercover :=
  QuasiCompactCover.of_isOpenMap (fun i => f.isOpenMap)

/-- Original line/descent category equivalence for every actual fppf
covering morphism onto an affine base, including non-affine sources. -/
@[expose] def equivalence : Line Y ≌ Datum f := by
  letI := cover_quasiCompact f
  exact AffineBaseFpqcDescent318.equivalence f

lemma functor_map {L K : Line Y} (h : L ⟶ K) :
    ((equivalence f).functor.map h).sheafHom = (Scheme.Modules.pullback f).map h := rfl
end AffineBaseFppfDescent318
