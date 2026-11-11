module
public import NormElementInIdeal318
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace PolynomialNonzeroIdealFinite318
open Polynomial
universe u v
variable (K : Type u) [Field K] (S : Type v) [CommRing S]
  [Algebra K S] [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
  [Module.Finite (Polynomial K) S]

/-- An actual nonzero polynomial in the contracted ideal makes the same
quotient finite over the field. The quotient by that polynomial is used
with its literal scalar map, not a new finite-dimensional model. -/
lemma finite_of_scalar (I : Ideal S) (p : Polynomial K) (hp : p≠0)
    (hmem : algebraMap (Polynomial K) S p∈I) : Module.Finite K (S⧸I) := by
  let J : Ideal (Polynomial K) := Ideal.span {p}
  have hJ : J≤I.comap (algebraMap (Polynomial K) S) :=
    Ideal.span_le.mpr (by intro a ha; obtain rfl := Set.mem_singleton_iff.mp ha; exact hmem)
  letI : Algebra (Polynomial K⧸J) (S⧸I) := Ideal.Quotient.algebraQuotientOfLEComap hJ
  letI : IsScalarTower (Polynomial K) (Polynomial K⧸J) (S⧸I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (Polynomial K⧸J) (S⧸I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (Polynomial K) (S⧸I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Polynomial K) I).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite (Polynomial K⧸J) (S⧸I) :=
    Module.Finite.of_restrictScalars_finite (Polynomial K) (Polynomial K⧸J) (S⧸I)
  letI : Module.Finite K (Polynomial K⧸J) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hp).basis
  exact Module.Finite.trans (Polynomial K⧸J) (S⧸I)

/-- A nonzero actual ideal on a finite free integral polynomial chart
has a finite field quotient. The determinant argument supplies the
polynomial instead of assuming a chosen annihilator or a degree bound. -/
lemma finite [IsDomain S] [Module.Free (Polynomial K) S] (I : Ideal S)
    (hI : I≠⊥) : Module.Finite K (S⧸I) := by
  obtain ⟨a,ha,hne⟩ := (I : Submodule S S).ne_bot_iff.mp hI
  obtain ⟨p,hp,hmem⟩ := NormElementInIdeal318.nonzero_scalar (Polynomial K) S I a ha hne
  exact finite_of_scalar K S I p hp hmem
end PolynomialNonzeroIdealFinite318
