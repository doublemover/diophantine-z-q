module
public import OriginalFullInertiaReconstruction318
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public section
noncomputable section
namespace NormalClosureGeometricPoints318
open AlgebraicGeometry CategoryTheory Polynomial LinearContactSquareclass318
open OriginalNormalClosureGalois318
variable (L : Type) [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- The original affine automorphism, contravariantly induced by the SAME
restriction of the original generic automorphism. -/
@[expose] def schemeMap (σ : Group L) : Spec (CommRingCat.of (Order L)) ⟶
    Spec (CommRingCat.of (Order L)) :=
  Spec.map (CommRingCat.ofHom (affineAction L σ).toRingHom)

@[expose] def point {F : Type} [Field F] (p : Order L →+* F) :
    Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (Order L)) :=
  Spec.map (CommRingCat.ofHom p)

@[expose] def coordinate {F : Type} [Field F] (p : Order L →+* F) : F :=
  p (algebraMap ℚ[X] (Order L) X)
@[expose] def contactValue {F : Type} [Field F] (p : Order L →+* F) (k : Fin 4) : F :=
  p (algebraMap ℚ[X] (Order L) (C (contacts k)))

/-- An actual geometric point over the exact original affine prime. -/
@[expose] def geometricPoint (P : Ideal (Order L)) [P.IsPrime] :
    Order L →+* AlgebraicClosure P.ResidueField :=
  (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
    (algebraMap (Order L) P.ResidueField)

lemma geometricPoint_kernel (P : Ideal (Order L)) [P.IsPrime] :
    RingHom.ker (geometricPoint L P) = P := by
  ext x
  change algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)
    (algebraMap (Order L) P.ResidueField x) = 0 ↔ x ∈ P
  constructor
  · intro h
    apply Ideal.algebraMap_residueField_eq_zero.mp
    apply (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.mpr h, map_zero]

variable {L} {F : Type} [Field F] (p : Order L →+* F)
  (P : Ideal (Order L)) (hker : RingHom.ker p = P)

include hker in
lemma inertia_iff (σ : Group L) : σ ∈ P.inertia (Group L) ↔
    p.comp (affineAction L σ).toRingHom = p := by
  rw [Ideal.mem_inertia]
  constructor
  · intro h
    apply RingHom.ext
    intro x
    have hx := h x
    rw [← hker] at hx
    change p (affineAction L σ x - x) = 0 at hx
    simpa only [map_sub, sub_eq_zero] using hx
  · intro h x
    rw [← hker]
    change p (affineAction L σ x - x) = 0
    have hx := RingHom.congr_fun h x
    change p (affineAction L σ x) = p x at hx
    rw [map_sub, hx, sub_self]

include hker in
/-- Full ideal inertia is precisely the stabilizer of the literal geometric
Spec-valued point, not merely the stabilizer of its topological support. -/
lemma scheme_fixed_iff (σ : Group L) :
    point L p ≫ schemeMap L σ = point L p ↔ σ ∈ P.inertia (Group L) := by
  rw [inertia_iff p P hker]
  unfold point schemeMap
  rw [← Spec.map_comp]
  constructor
  · intro h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  · intro h
    congr 1
    exact CommRingCat.hom_ext h

include hker in
/-- The original residue coordinate detects exactly the labeled polynomial
prime. Nonrational closed primes cannot be silently counted as contact primes. -/
lemma contact_iff (q : ℚ[X]) (hq : Prime q)
    (hc : P.under ℚ[X] = Ideal.span {q}) (k : Fin 4) :
    Associated q (X - C (contacts k)) ↔ coordinate L p = contactValue L p k := by
  have hz : p (algebraMap ℚ[X] (Order L) (X - C (contacts k))) = 0 ↔
      coordinate L p = contactValue L p k := by
    simp only [map_sub, sub_eq_zero, coordinate, contactValue]
  have hd : q ∣ (X - C (contacts k)) ↔
      p (algebraMap ℚ[X] (Order L) (X - C (contacts k))) = 0 := by
    rw [← Ideal.mem_span_singleton, ← hc]
    change algebraMap ℚ[X] (Order L) (X - C (contacts k)) ∈ P ↔ _
    rw [← hker]
    all_goals rfl
  constructor
  · intro h
    exact hz.mp (hd.mp h.dvd)
  · intro h
    exact hq.irreducible.associated_of_dvd (irreducible_X_sub_C _) (hd.mpr (hz.mpr h))
end NormalClosureGeometricPoints318
