module
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public section
noncomputable section

open Polynomial

namespace SelectedLiteralRatFuncScalar318

variable {K L : Type*} [Field K] [Field L]

@[expose] def polynomialMap (f : K→+*L) : K[X]→+*RatFunc L :=
  (algebraMap L[X] (RatFunc L)).comp (Polynomial.mapRingHom f)

theorem polynomialMap_injective (f : K→+*L) : Function.Injective (polynomialMap f) :=
  (IsFractionRing.injective L[X] (RatFunc L)).comp (Polynomial.map_injective f f.injective)

/-- The entire chosen coefficient field changes inside the rational
function field via the actual coefficient embedding, preserving X. -/
@[expose] def map (f : K→+*L) : RatFunc K→+*RatFunc L :=
  IsFractionRing.lift (polynomialMap_injective f)

theorem map_polynomial (f : K→+*L) (a : K[X]) :
    map f (algebraMap K[X] (RatFunc K) a) =
      algebraMap L[X] (RatFunc L) (a.map f) := by
  rw [map,IsFractionRing.lift_algebraMap]
  rfl

theorem map_X (f : K→+*L) : map f (RatFunc.X:RatFunc K)=(RatFunc.X:RatFunc L) := by
  rw [←RatFunc.algebraMap_X,map_polynomial,Polynomial.map_X,RatFunc.algebraMap_X]

end SelectedLiteralRatFuncScalar318

#print axioms SelectedLiteralRatFuncScalar318.map_polynomial
#print axioms SelectedLiteralRatFuncScalar318.map_X
