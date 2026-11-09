module
public import ModuleRestrictionCoverFaithful318
public section
noncomputable section
namespace OriginalDoubleCoverFaithful318
open AlgebraicGeometry CategoryTheory
open ActualOverlapDiagram318 OriginalDoubleOpenCover318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {M N : (Double f).Modules} {a b : M ⟶ N}

/-- Equality pulled back to an actual restricted double gives equality
on the corresponding whole open of the original double. -/
lemma restriction_eq (U : Y.Opens)
    (h : (Scheme.Modules.pullback (doubleMap f U)).map a =
      (Scheme.Modules.pullback (doubleMap f U)).map b) :
    (Scheme.Modules.restrictFunctor (baseOpen f U).ι).map a =
      (Scheme.Modules.restrictFunctor (baseOpen f U).ι).map b := by
  have hp : (Scheme.Modules.pullback (baseOpen f U).ι).map a =
      (Scheme.Modules.pullback (baseOpen f U).ι).map b := by
    apply SheafIsoTransport318.pullback_injective (iso f U)
    let q := PullbackPathComposition318.iso (iso f U).hom (baseOpen f U).ι
      (doubleMap f U) (iso_hom_ι f U)
    apply (cancel_mono q.hom.app N).mp
    have ha := q.hom.naturality a
    have hb := q.hom.naturality b
    simp only [Functor.comp_map] at ha hb
    rw [ha,hb,h]
  apply (cancel_mono (Scheme.Modules.restrictFunctorIsoPullback (baseOpen f U).ι).hom.app N).mp
  rw [(Scheme.Modules.restrictFunctorIsoPullback (baseOpen f U).ι).hom.naturality a,
    (Scheme.Modules.restrictFunctorIsoPullback (baseOpen f U).ι).hom.naturality b,hp]

/-- The actual restricted categorical doubles jointly detect every
original overlap morphism. Coverage is proved by the original base affine
basis and the actual Cartesian double comparison. -/
lemma hom_ext (h : ∀ U : Y.affineOpens,
    (Scheme.Modules.pullback (doubleMap f U.1)).map a =
      (Scheme.Modules.pullback (doubleMap f U.1)).map b) : a = b :=
  ModuleRestrictionCoverFaithful318.hom_ext (fun U : Y.affineOpens => baseOpen f U.1)
    (cover f) (fun U => restriction_eq f U.1 (h U))
end OriginalDoubleCoverFaithful318
