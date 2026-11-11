module
public import CyclicQuotientIntertwiner318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace CyclicQuotientFiniteFlat318
open AlgebraicGeometry CategoryTheory CyclicQuotientEvaluation318
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
variable (ρ : A →ₐ[R] Module.End R M) (v : M)

abbrev scheme : Scheme := Spec (CommRingCat.of (A ⧸ ideal ρ v))
abbrev into : scheme ρ v ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal ρ v)))
abbrev projection : scheme ρ v ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ ideal ρ v)))

/-- The family sits in the actual source affine scheme by the original
quotient map, and retains the entire scheme-theoretic ideal. -/
instance closed : IsClosedImmersion (into ρ v) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable {ι : Type u} [Fintype ι] (b : Basis ι R M)
  (h : Function.Surjective (evaluation ρ v))
include b h

lemma module_finite : Module.Finite R (A ⧸ ideal ρ v) :=
  Module.Finite.of_basis (CyclicQuotientKernel318.quotientBasis ρ v b h)

lemma module_free : Module.Free R (A ⧸ ideal ρ v) :=
  Module.Free.of_basis (CyclicQuotientKernel318.quotientBasis ρ v b h)

lemma module_flat : Module.Flat R (A ⧸ ideal ρ v) := by
  letI := module_free ρ v b h
  exact Module.Flat.of_free

/-- A cyclic representation on a finite free module gives an ACTUAL
finite flat quotient family over the original ring. This does not assume
Cartier regularity, choose a fixed source line, or pass to geometric points. -/
lemma finite : IsFinite (projection ρ v) := by
  letI := module_finite ρ v b h
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

lemma flat : Flat (projection ρ v) := by
  letI := module_flat ρ v b h
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
end CyclicQuotientFiniteFlat318
