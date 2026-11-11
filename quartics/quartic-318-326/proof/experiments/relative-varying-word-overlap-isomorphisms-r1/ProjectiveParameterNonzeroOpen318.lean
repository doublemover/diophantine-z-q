module
public import ProjectiveParameterZeroCoordinates318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace ProjectiveParameterNonzeroOpen318
open TopologicalSpace
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

/-- A literal finite union of principal opens in the actual section
parameter spectrum, excluding its zero-section ideal. -/
@[expose] def locus : Opens (PrimeSpectrum A) :=
  ⟨⋃ i : Fin F.size, (PrimeSpectrum.basicOpen
      (ProjectiveParameterZeroCoordinates318.coordinate R P i) : Set (PrimeSpectrum A)),
    isOpen_iUnion (fun i => (PrimeSpectrum.basicOpen
      (ProjectiveParameterZeroCoordinates318.coordinate R P i)).isOpen)⟩

lemma mem_locus (p : PrimeSpectrum A) : p ∈ locus R P ↔
    ¬ ProjectiveParameterZeroCoordinates318.zeroIdeal R P ≤ p.asIdeal := by
  change (∃ i,ProjectiveParameterZeroCoordinates318.coordinate R P i ∉ p.asIdeal) ↔ _
  rw [ProjectiveParameterZeroCoordinates318.zeroIdeal,Ideal.span_le]
  simp only [Set.range_subset_iff]
  exact not_forall.symm

variable (K : Type w) [Field K] [Algebra R K]

/-- The genuine spectrum point of the actual algebra map to a field. -/
@[expose] def fieldPoint (a : A →ₐ[R] K) : PrimeSpectrum A :=
  PrimeSpectrum.comap a.toRingHom ⟨⊥,inferInstance⟩

/-- Membership is exactly nonvanishing of the SAME represented section
on every field test. This is not yet the relative-flatness theorem. -/
theorem fieldPoint_mem_iff (a : A →ₐ[R] K) :
    fieldPoint R P K a ∈ locus R P ↔ ProjectiveSectionParameter318.points R P K a≠0 := by
  rw [mem_locus]
  change ¬ ProjectiveParameterZeroCoordinates318.zeroIdeal R P ≤ RingHom.ker a.toRingHom ↔ _
  rw [ProjectiveParameterZeroCoordinates318.zeroIdeal_le_kernel_iff]
end ProjectiveParameterNonzeroOpen318
