module
public import ContactGlobalProper318
public import BivariateIntegral318
public import Mathlib.LinearAlgebra.FreeModule.PID

public section
noncomputable section
namespace ContactWholeInfinityAlgebra318
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev Source := ContactKummerOrder318.OpenOrder c
local instance : IsDomain (Source c) := ContactKummerOpenDomain318.open_domain c
local instance : Module.Finite ContactKummerOrder318.OpenBase (Source c) :=
  (ContactKummerOrder318.open_finite_free_etale c).1
local instance : Algebra.Etale ContactKummerOrder318.OpenBase (Source c) :=
  (ContactKummerOrder318.open_finite_free_etale c).2.2

/-- The exact whole infinity coordinate is 1/t in the original source,
not the t-action reused on a ring with the same underlying carrier. -/
def polynomialMap : ℚ[X] →+* Source c := ContactReciprocalCover318.polynomialMap (Source c)

lemma polynomialMap_injective : Function.Injective (polynomialMap c) := by
  exact (FaithfulSMul.algebraMap_injective ContactKummerOrder318.OpenBase (Source c)).comp
    (ContactReciprocalBase318.reciprocalEquiv.symm.injective.comp
      (IsLocalization.injective (M:=Submonoid.powers ContactReciprocalBase318.denominator) _
        (by rintro x ⟨m,rfl⟩
            exact mem_nonZeroDivisors_iff_ne_zero.mpr
              (pow_ne_zero m ContactReciprocalBase318.denominator_ne_zero))))

local instance reciprocalAlgebra : Algebra ℚ[X] (Source c) := (polynomialMap c).toAlgebra

/-- Integral closure over the ENTIRE polynomial infinity chart. No factor
of the reciprocal contact denominator is inverted in this base. -/
abbrev Ring := integralClosure ℚ[X] (Source c)

instance finite : Module.Finite ℚ[X] (Ring c) :=
  (ContactReciprocalCover318.finite_normal_model (Source c)).1

lemma algebraMap_injective : Function.Injective (algebraMap ℚ[X] (Ring c)) := by
  intro a b h
  exact polynomialMap_injective c (congrArg Subtype.val h)

instance flat : Module.Flat ℚ[X] (Ring c) :=
  BivariateIntegral318.flat_of_injective (R := ℚ[X]) (S := Ring c) (algebraMap_injective c)

private theorem free_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsPrincipalIdealRing R] [IsDomain S] [Algebra R S]
    [Module.Finite R S] (h : Function.Injective (algebraMap R S)) : Module.Free R S := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr h
  exact Module.free_of_finite_type_torsion_free' (R := R) (M := S)

instance free : Module.Free ℚ[X] (Ring c) :=
  free_of_injective (R := ℚ[X]) (S := Ring c) (algebraMap_injective c)

/-- Actual reciprocal coordinate retained in the original ambient source. -/
lemma coordinate : ((algebraMap ℚ[X] (Ring c) X).val : Source c) =
    algebraMap ContactKummerOrder318.OpenBase (Source c)
      (↑ContactReciprocalBase318.tUnit⁻¹) :=
  ContactReciprocalCover318.polynomial_coordinate (Source c)
end ContactWholeInfinityAlgebra318
