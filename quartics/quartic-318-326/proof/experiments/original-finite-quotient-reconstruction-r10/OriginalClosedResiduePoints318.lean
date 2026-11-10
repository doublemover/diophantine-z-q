module
public import NormalClosureGeometricPoints318
public import Mathlib.RingTheory.Jacobson.Ring
public section
noncomputable section
namespace OriginalClosedResiduePoints318
open Polynomial OriginalNormalClosureGalois318
variable (L : Type) [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

/-- Every actual prime above a nonzero polynomial prime has a geometric point
in ONE fixed algebraically closed characteristic-zero field. The kernel is
exactly the original prime, including nonrational closed primes. -/
theorem exists_point (q : ℚ[X]) (hq : Prime q) (P : Ideal (Order L)) [P.IsPrime]
    (hc : P.under ℚ[X] = Ideal.span {q}) :
    ∃ p : Order L →+* Ω, RingHom.ker p = P := by
  letI : (Ideal.span {q}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  letI : P.LiesOver (Ideal.span {q}) := ⟨hc.symm⟩
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {q})
  letI : Algebra ℚ (Order L) :=
    ((algebraMap ℚ[X] (Order L)).comp (algebraMap ℚ ℚ[X])).toAlgebra
  letI : IsScalarTower ℚ ℚ[X] (Order L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.FiniteType ℚ (Order L) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℚ ℚ[X])
      (inferInstance : Algebra.FiniteType ℚ[X] (Order L))
  letI : Algebra ℚ P.ResidueField :=
    ((algebraMap (Order L) P.ResidueField).comp (algebraMap ℚ (Order L))).toAlgebra
  letI : IsScalarTower ℚ (Order L) P.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.FiniteType ℚ P.ResidueField :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℚ (Order L))
      (inferInstance : Algebra.FiniteType (Order L) P.ResidueField)
  letI : Module.Finite ℚ P.ResidueField :=
    finite_of_finite_type_of_isJacobsonRing ℚ P.ResidueField
  let e : P.ResidueField →ₐ[ℚ] Ω := IsAlgClosed.lift
  refine ⟨e.toRingHom.comp (algebraMap (Order L) P.ResidueField), ?_⟩
  ext x
  change e (algebraMap (Order L) P.ResidueField x) = 0 ↔ x ∈ P
  constructor
  · intro h
    apply Ideal.algebraMap_residueField_eq_zero.mp
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.mpr h, map_zero]
end OriginalClosedResiduePoints318
