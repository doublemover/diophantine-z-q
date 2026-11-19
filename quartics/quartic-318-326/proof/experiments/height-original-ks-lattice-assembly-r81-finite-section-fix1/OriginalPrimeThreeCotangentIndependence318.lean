module
public import OriginalPrimeThreeFirstOrderPoint318
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace OriginalPrimeThreeCotangentIndependence318

section CertificateToCotangent
variable {A : Type*} [CommRing A] (I : Ideal A) (r : Fin 3 → A)
variable (hr : ∀ i, r i ∈ I)

@[expose] def cotangentClasses (i : Fin 3) : I.Cotangent :=
  I.toCotangent ⟨r i, hr i⟩

/-- The relation certificate yields linear independence in the literal
module I/I² over A/I, not only independence of formal derivative vectors. -/
theorem classes_linearIndependent
    (hind : ∀ a : Fin 3 → A, (∑ i, a i * r i) ∈ I ^ 2 → ∀ i, a i ∈ I) :
    LinearIndependent (A ⧸ I) (cotangentClasses I r hr) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  choose b hb using fun i => Ideal.Quotient.mk_surjective (a i)
  have hh : I.toCotangent (∑ i, b i • (⟨r i, hr i⟩ : I)) = 0 := by
    calc
      _ = ∑ i, b i • cotangentClasses I r hr i := by
        simp only [map_sum, map_smul, cotangentClasses]
      _ = ∑ i, a i • cotangentClasses I r hr i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hb i]
        exact (IsScalarTower.algebraMap_smul A (A ⧸ I) I.Cotangent
          (b i) (cotangentClasses I r hr i)).symm
      _ = 0 := ha
  have hmem : (∑ i, b i * r i) ∈ I ^ 2 := by
    simpa using (I.toCotangent_eq_zero _).mp hh
  intro i
  rw [← hb i, Ideal.Quotient.eq_zero_iff_mem]
  exact hind b hmem i
end CertificateToCotangent

open OriginalPrimeThreeFirstOrderPoint318
abbrev pointIdeal : Ideal Closure := RingHom.ker normalizedPoint

/-- A maximal ideal on the actual normalized finite chart, proved using
the constructed surjection onto the constructed residue field F9. -/
instance pointIdeal_maximal : pointIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective normalizedPoint normalizedPoint_surjective

local instance residueQuotientField : Field (Closure ⧸ pointIdeal) :=
  Ideal.Quotient.field pointIdeal
local instance closureNoetherian : IsNoetherianRing Closure :=
  OriginalIntegerFiniteClosure318.closure_noetherian OriginalPrimeThreeActualQuotient318.twist

@[expose] def actualCotangentClasses (i : Fin 3) : pointIdeal.Cotangent :=
  cotangentClasses pointIdeal normalizedRoot normalized_root_mem_point i

theorem actual_cotangent_linearIndependent :
    LinearIndependent (Closure ⧸ pointIdeal) actualCotangentClasses := by
  apply classes_linearIndependent pointIdeal normalizedRoot normalized_root_mem_point
  intro a ha i
  exact RingHom.mem_ker.mpr (normalized_roots_independent_mod_square a ha i)

local instance cotangentFinite : Module.Finite (Closure ⧸ pointIdeal) pointIdeal.Cotangent :=
  Module.Finite.of_restrictScalars_finite Closure (Closure ⧸ pointIdeal) pointIdeal.Cotangent

/-- A genuine numerical lower bound on the cotangent dimension of the
actual maximal ideal of the normalized affine chart. Equality with three,
localization comparison, and local Krull dimension remain separate steps. -/
theorem actual_cotangent_finrank_ge_three :
    3 ≤ Module.finrank (Closure ⧸ pointIdeal) pointIdeal.Cotangent := by
  simpa only [Fintype.card_fin] using actual_cotangent_linearIndependent.fintype_card_le_finrank

end OriginalPrimeThreeCotangentIndependence318
