module
public import SelectedCanonicalCompactScalar318
public import SelectedGenericCompactNormalization318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedCanonicalCompactScalar318

namespace SelectedRationalCompactScalarLift318

variable {U V Y C : Scheme} (a : U ⟶ V) (v : V ⟶ ProjectiveJLine318.scheme ℚ)
  [IsFinite a] [IsOpenImmersion v] [QuasiCompact v]
  (b : Y ⟶ V) (i : Y ⟶ C) [IsOpenImmersion i]
  (j : C ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite j]
  [IsIntegral U] [IsIntegral C]
  (e : U ≅ Y) (he : e.hom ≫ b = a) (hi : i ≫ j = b ≫ v)
  (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W))

local notation "j₀" => (a ≫ v).fromNormalization

variable (L : Type) [Field L] [Algebra ℚ L]

/-- Apply the actual original ordinary-to-compact comparison before
extending constants. Both scalar sources are the ENTIRE canonical
pullbacks along this chosen field map from ℚ. -/
@[expose] def liftCompact :
    source ℚ L j₀ ≅ source ℚ L j :=
  sourceIso ℚ L j₀ j
    (SelectedGenericCompactNormalization318.rationalJ a v b i j e he hi normal)
    (SelectedGenericCompactNormalization318.rationalJ_over a v b i j e he hi normal)

/-- The comparison at the selected field lift still respects the
same j-map. The ordinary-normalization constructor provides the
old over-j equation, and the universal projective pullback forces
the new one. This does not choose a complex component. -/
@[reassoc] theorem liftCompact_over :
    (liftCompact a v b i j e he hi normal L).hom ≫ modularMap ℚ L j =
      modularMap ℚ L j₀ :=
  sourceIso_over ℚ L j₀ j
    (SelectedGenericCompactNormalization318.rationalJ a v b i j e he hi normal)
    (SelectedGenericCompactNormalization318.rationalJ_over a v b i j e he hi normal)

theorem literal_lift_pullback :
    IsPullback (sourceProjection ℚ L j₀) (modularMap ℚ L j₀) j₀
      (SelectedProjectiveJScalar318.scalarMap (algebraMap ℚ L)) :=
  modular_pullback ℚ L j₀

end SelectedRationalCompactScalarLift318

#print axioms SelectedRationalCompactScalarLift318.liftCompact_over
#print axioms SelectedRationalCompactScalarLift318.literal_lift_pullback
