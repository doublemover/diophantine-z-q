module
public import FiniteComplexSchemeRank318
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace ConnectedFiniteFlatFiberRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {X Y : Scheme} (f : X⟶Y) [IsFinite f] [Flat f]
  [LocallyOfFinitePresentation f] [PreconnectedSpace Y]
variable (p : Spec (CommRingCat.of ℂ)⟶Y)
local instance : Algebra ℂ Γ(pullback f p,⊤) :=
  FiniteEtaleComplexSections318.algebra (pullback.snd f p)
/-- The genuine locally constant native finite-flat rank on a connected
base is determined by its WHOLE complex fiber, not by its support. -/
lemma rank_eq_fiber (y : Y) :
    f.finrank y=Module.finrank ℂ Γ(pullback f p,⊤) := by
  calc
    f.finrank y=f.finrank (p (IsLocalRing.closedPoint ℂ)) :=
      f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _=(pullback.snd f p).finrank (IsLocalRing.closedPoint ℂ) :=
      (Scheme.Hom.finrank_pullback_snd f p _).symm
    _=Module.finrank ℂ Γ(pullback f p,⊤) :=
      FiniteComplexSchemeRank318.rank_eq _ _
end ConnectedFiniteFlatFiberRank318
