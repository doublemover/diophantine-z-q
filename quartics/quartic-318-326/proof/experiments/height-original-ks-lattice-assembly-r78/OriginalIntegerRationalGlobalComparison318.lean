module
public import OriginalIntegerRationalIntersectionProjections318
public import OriginalIntegerRationalOverlapEquality318
public import OriginalIntegerRationalTwoCover318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace OriginalIntegerRationalGlobalComparison318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OriginalIntegerRationalGlobalRegularity318
open OriginalIntegerRationalTwoCover318
open OriginalIntegerRationalIntersectionProjections318
variable (c : Fin 4 → ℚˣ)

@[expose] def localMap (i : Bool) : (rationalCover c).X i ⟶ Original c := by
  cases i with
  | false => exact (finiteIso c).hom ≫
      OriginalIntegerRationalSourceIdentification318.rationalFiberChart c
  | true => exact (infinityIso c).hom ≫
      OriginalIntegerRationalReciprocalChart318.fiberChart c

/-- Compatibility on the full actual cover intersection, proved by its
TWO projection identities and the literal overlap-arrow equality. -/
theorem cross_compatibility :
    pullback.fst ((rationalCover c).f false) ((rationalCover c).f true) ≫ localMap c false =
    pullback.snd ((rationalCover c).f false) ((rationalCover c).f true) ≫ localMap c true := by
  change _ ≫ ((finiteIso c).hom ≫ _) = _ ≫ ((infinityIso c).hom ≫ _)
  rw [← Category.assoc, ← finite_projection, Category.assoc,
    OriginalIntegerRationalOverlapEquality318.actual_overlap_equality,
    ← Category.assoc, infinity_projection, Category.assoc]

theorem compatibility (i j : Bool) :
    pullback.fst ((rationalCover c).f i) ((rationalCover c).f j) ≫ localMap c i =
    pullback.snd ((rationalCover c).f i) ((rationalCover c).f j) ≫ localMap c j := by
  cases i <;> cases j
  · exact congrArg (fun f => f ≫ localMap c false)
      ((cancel_mono ((rationalCover c).f false)).mp pullback.condition)
  · exact cross_compatibility c
  · apply (cancel_epi (pullbackSymmetry ((rationalCover c).f false)
      ((rationalCover c).f true)).hom).mp
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] using (cross_compatibility c).symm
  · exact congrArg (fun f => f ≫ localMap c true)
      ((cancel_mono ((rationalCover c).f true)).mp pullback.condition)

/-- The global comparison from the ACTUAL rational base change to the
original model, descended from the entire two-chart cover. This definition
does not yet assert that the comparison is an isomorphism. -/
@[expose] def comparison : rationalFiber c ⟶ Original c :=
  (rationalCover c).glueMorphisms (localMap c) (compatibility c)

@[reassoc] theorem restriction (i : Bool) :
    (rationalCover c).f i ≫ comparison c = localMap c i :=
  (rationalCover c).ι_glueMorphisms _ _ i

/-- Uniqueness is a whole-cover assertion, not merely equality at the
function-field point. -/
theorem comparison_unique (f : rationalFiber c ⟶ Original c)
    (h : ∀ i, (rationalCover c).f i ≫ f = localMap c i) : f = comparison c := by
  apply (rationalCover c).hom_ext
  intro i
  rw [h i, restriction]

end OriginalIntegerRationalGlobalComparison318
