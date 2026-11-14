module
public import OriginalTwoOpenReducedCocycle318
public section
noncomputable section
namespace OriginalHOnePointedSurjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 AffineHOnePointedDeformation318
universe u
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ base R)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (L : Deformation R p)
/-- The coefficient is the unique original section logarithm of the actual
normalized transition of this particular original pointed line. -/
@[expose] def coefficient : Γ(X,U ⊓ V) := by
  letI : IsAffine (U ⊓ V).toScheme := hUV
  exact OriginalOpenUnitLogarithm318.log R p (U ⊓ V)
    (OriginalTwoOpenReducedCocycle318.overlapUnit p U V hU hV L)
/-- The OLD representative cocycle, unchanged: actual first projection followed
by the actual epsilon unit construction. -/
@[expose] def originalCocycle (x : Γ(X,U ⊓ V)) : UnitTransitionCocycle318.Cocycle
    (StructureUnitsSheaf318.units (thickening R p)).obj (thickOpens p U V) :=
  InfinitesimalUnitCocycle318.cocycle (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p)
    (DualNumberInfinitesimalLines318.epsilon_square R p) (thickOpens p U V)
    (AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R))
      (TwoOpenAdditiveCocycle318.opens U V) (thickOpens p U V) (fun _ => le_rfl)
      (TwoOpenAdditiveCocycle318.cocycle U V x))
lemma original_forward (x : Γ(X,U ⊓ V)) : (originalCocycle p U V x).transition false true =
    InfinitesimalUnitCocycle318.unit (thickening R p)
      (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p)
      ((pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V))
      ((pullback.fst p (structureMap R)).app (U ⊓ V) x) := by
  change InfinitesimalUnitCocycle318.unit (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p)
    (DualNumberInfinitesimalLines318.epsilon_square R p) _
    ((pullback.fst p (structureMap R)).appLE (U ⊓ V)
      ((pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V)) _
      ((TwoOpenAdditiveCocycle318.cocycle U V x).transition false true)) = _
  rw [TwoOpenAdditiveCocycle318.forward, Scheme.Hom.appLE_eq_app]
lemma cocycle_eq : OriginalTwoOpenReducedCocycle318.cocycle p U V hU hV L =
    originalCocycle p U V (coefficient p U V hU hV hUV L) := by
  letI : IsAffine (U ⊓ V).toScheme := hUV
  apply TwoOpenUnitCocycleExt318.ext
  rw [original_forward]
  exact ((OriginalOpenUnitLogarithm318.exp_original R p (U ⊓ V) _).symm.trans
    (OriginalOpenUnitLogarithm318.exp_log R p (U ⊓ V)
      (OriginalTwoOpenReducedCocycle318.overlapUnit p U V hU hV L)
      (OriginalTwoOpenReducedCocycle318.overlapUnit_reduces p U V hU hV L))).symm
variable (hc : U ⊔ V = ⊤)
/-- Every original pointed line is isomorphic to the original representative
constructed from its actual overlap logarithm. -/
@[expose] def lineIso : L.line.object ≅ CocycleModule318.object (thickOpens p U V)
    (originalCocycle p U V (coefficient p U V hU hV hUV L)) :=
  OriginalTwoOpenReducedCocycle318.reconstruction p U V hU hV L hc ≪≫
    eqToIso (congrArg (CocycleModule318.object (thickOpens p U V)) (cocycle_eq p U V hU hV hUV L))
lemma representative_class : PointedLineDeformation318.classOf (reduction R p) L =
    representativeClass p U V hc (coefficient p U V hU hV hUV L) := by
  change PointedLineDeformation318.classOf (reduction R p) L =
    PointedLineDeformation318.classOf (reduction R p)
      (DualNumberInfinitesimalLines318.deformation R p (thickOpens p U V) (thick_cover p U V hc)
        (AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R))
          (TwoOpenAdditiveCocycle318.opens U V) (thickOpens p U V) (fun _ => le_rfl)
          (TwoOpenAdditiveCocycle318.cocycle U V (coefficient p U V hU hV hUV L))))
  exact DualNumberPointedKernel318.class_eq_of_iso p L _ (lineIso p U V hU hV hUV L hc)
variable [IsIntegral X]
include hUV in
/-- Surjectivity of the EXISTING original global-H1 map onto ALL actual
pointed first-order line classes, not merely those initially given by cocycles.
No injectivity, tangent representation or norm statement is inferred. -/
lemma map_surjective : Function.Surjective (AffineHOnePointedDeformation318.map p U V hU hV hc) := by
  intro z
  induction z using Quotient.inductionOn with
  | h L =>
    refine ⟨AffineCoverHOnePresentation318.boundary U V hc (coefficient p U V hU hV hUV L), ?_⟩
    rw [AffineHOnePointedDeformation318.map_boundary]
    exact (representative_class p U V hU hV hUV L hc).symm
end OriginalHOnePointedSurjection318
