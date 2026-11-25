module
public import OriginalR47ChosenRoundTrait318
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public section
noncomputable section

namespace OriginalR47ArithmeticCentreFG318

open AlgebraicGeometry CategoryTheory
open OriginalR47IsolatedCentreCover318 (Centre)
open OriginalR47GlobalCentreRees318
open OriginalR47ChosenRoundTrait318 (oldScalar old_scalar_read)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of R))
variable {Z : Set X} (pick : ∀ z : Z, Centre Z z)

/-- The actual named old affine centre contracts to the arithmetic
prime of the same original point, with the exact structural scalar
used in the strict attached Rees trait. Nothing is chosen from χ. -/
theorem prime_read (z : Z) :
    letI : Algebra R (A pick z) := oldScalar s pick z
    (marked pick z).asIdeal.comap (algebraMap R (A pick z)) = (s z.val).asIdeal := by
  let : Algebra R (A pick z) := oldScalar s pick z
  have hz := congrArg
    (fun l : Spec (A pick z) ⟶ Spec (CommRingCat.of R) => l (marked pick z))
    (old_scalar_read s pick z)
  have hz' : Spec.algebraMap R (A pick z) (marked pick z) = s z.val := by
    simpa only [Scheme.Hom.comp_apply,marked_read pick z] using hz
  exact congrArg PrimeSpectrum.asIdeal hz'

variable [IsNoetherianRing R] [LocallyOfFiniteType s]

/-- Finite generation is a consequence of the actual arithmetic scalar,
not of a second algebra structure on the old affine ring or a caller
assertion that the marked centre ideal is finitely generated. -/
theorem fg (z : Z) : (marked pick z).asIdeal.FG := by
  let T := A pick z
  let : Algebra R T := oldScalar s pick z
  have hread : Spec.algebraMap R T = affineArrow pick z ≫ s := old_scalar_read s pick z
  have hft : LocallyOfFiniteType (Spec.algebraMap R T) := hread.symm ▸
    (inferInstance : LocallyOfFiniteType (affineArrow pick z ≫ s))
  have hfinite : (algebraMap R T).FiniteType :=
    (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp hft
  let : Algebra.FiniteType R T := RingHom.finiteType_algebraMap.mp hfinite
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
  exact IsNoetherian.noetherian (marked pick z).asIdeal

end OriginalR47ArithmeticCentreFG318

#print axioms OriginalR47ArithmeticCentreFG318.prime_read
#print axioms OriginalR47ArithmeticCentreFG318.fg
