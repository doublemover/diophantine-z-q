module
public import OriginalInfinitesimalNormCocycle318
public section
noncomputable section
namespace OriginalTwoOpenNormRepresentative318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 OriginalThickenedOpenSections318
open TwoOpenAdditiveCocycle318 OriginalInfinitesimalNormCocycle318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (U V : Y.Opens)
/-- All four OLD source transitions, on the literal entire inverse images.
Boolean elimination supplies the carrier identities rather than an unproved
conversion between differently presented cover functions. -/
@[expose] def preimageCocycle (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    InfinitesimalUnitCocycle318.AdditiveCocycle X (fun i => f ⁻¹ᵁ opens U V i) where
  transition i j := by
    cases i <;> cases j <;>
      exact (TwoOpenAdditiveCocycle318.cocycle (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) x).transition _ _
  diagonal i := by
    cases i <;> exact (TwoOpenAdditiveCocycle318.cocycle (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) x).diagonal _
  triple i j k := by
    cases i <;> cases j <;> cases k <;>
      exact (TwoOpenAdditiveCocycle318.cocycle (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) x).triple _ _ _
lemma preimage_forward (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    (preimageCocycle f U V x).transition false true = x :=
  TwoOpenAdditiveCocycle318.forward (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) x
lemma original_source_transitions (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) (i j : Bool) :
    HEq ((OriginalInfinitesimalNormCocycle318.sourceCocycle R p f (opens U V)
        (preimageCocycle f U V x)).transition i j)
      ((OriginalHOnePointedSurjection318.originalCocycle p (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) x).transition i j) := by
  cases i <;> cases j <;>
    simp only [OriginalInfinitesimalNormCocycle318.sourceCocycle,preimageCocycle,
      OriginalHOnePointedSurjection318.originalCocycle, InfinitesimalUnitCocycle318.cocycle,
      AdditiveCocycleRefinement318.cocycle,OriginalThickenedNormTraceSquare318.sectionUnit,
      AffineHOnePointedDeformation318.thickOpens,opens,Scheme.Hom.appLE_eq_app]
  all_goals rfl
/-- The genuine norm of the OLD source representative has ALL four target
transitions equal to the OLD target representative of the OLD trace. -/
lemma norm_cocycle (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    normCocycle R p q f hY hfinite (opens U V) (preimageCocycle f U V x) =
      OriginalHOnePointedSurjection318.originalCocycle q U V
        (OpenDominantTrace318.trace f hY hfinite (U ⊓ V) x) := by
  apply TwoOpenUnitCocycleExt318.ext
  rw [norm_transition,OriginalHOnePointedSurjection318.original_forward]
  change OriginalThickenedNormTraceSquare318.sectionUnit R q (U ⊓ V)
    (OpenDominantTrace318.trace f hY hfinite (U ⊓ V) ((preimageCocycle f U V x).transition false true)) = _
  rw [preimage_forward]
  all_goals rfl
variable (hc : U ⊔ V = ⊤)
/-- A pointed line constructed by actually norming and gluing the original
source transitions, before any use of cohomological transfer. -/
@[expose] def normDeformation (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) : Deformation R q :=
  OriginalInfinitesimalNormCocycle318.deformation R p q f hY hfinite (opens U V)
    (preimageCocycle f U V x) (TwoOpenAdditiveCocycle318.cover U V hc)
lemma norm_class (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    PointedLineDeformation318.classOf (reduction R q) (normDeformation p q f hY hfinite U V hc x) =
      AffineHOnePointedDeformation318.representativeClass q U V hc
        (OpenDominantTrace318.trace f hY hfinite (U ⊓ V) x) := by
  apply DualNumberPointedKernel318.class_eq_of_iso q
  exact eqToIso (congrArg (CocycleModule318.object (AffineHOnePointedDeformation318.thickOpens q U V))
    (norm_cocycle p q f hY hfinite U V x))
end OriginalTwoOpenNormRepresentative318
