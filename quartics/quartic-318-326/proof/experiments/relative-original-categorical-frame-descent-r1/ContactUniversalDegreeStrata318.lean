module
public import ContactUniversalNonzeroFinite318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace ContactUniversalDegreeStrata318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "B" => ContactUniversalNonzeroFamily318.base R c L hz
local notation "π" => ContactUniversalNonzeroFamily318.projection R c L hz
local instance : IsFinite π := ContactUniversalNonzeroFinite318.finite R c L hz
local instance : Flat π := ContactUniversalNonzeroFlat318.flat R c L hz

/-- Degree is the ACTUAL finite-flat morphism rank of the original zero
family, not a prescribed integer or the number of reduced fiber points. -/
abbrev degree : B → ℕ := π.finrank
lemma degree_locally_constant : IsLocallyConstant (degree R c L hz) :=
  π.isLocallyConstant_finrank

/-- Canonical open-and-closed degree loci of the actual nonzero parameter
space. Different components are not silently assumed to have equal degree. -/
@[expose] def locus (n : ℕ) : B.Opens :=
  ⟨{x | degree R c L hz x=n},(degree_locally_constant R c L hz).isOpen_fiber n⟩
lemma locus_closed (n : ℕ) : IsClosed (locus R c L hz n : Set B) :=
  (degree_locally_constant R c L hz).isClosed_fiber n
lemma mem_locus (n : ℕ) (x : B) : x∈locus R c L hz n ↔ degree R c L hz x=n := Iff.rfl

/-- Rank follows genuine arbitrary base change of the SAME finite flat
family, not a chosen isomorphism of finite point sets. -/
lemma degree_base_change {T : Scheme.{0}} (f : T ⟶ B) (t : T) :
    (pullback.snd π f).finrank t=degree R c L hz (f t) :=
  Scheme.Hom.finrank_pullback_snd π f t

/-- The original residue-field fiber measures the very same degree. -/
lemma degree_fiber (y : B) (z : Spec (B.residueField y)) :
    (π.fiberToSpecResidueField y).finrank z=degree R c L hz y := by
  change (pullback.snd π (B.fromSpecResidueField y)).finrank z=_
  rw [degree_base_change,Scheme.fromSpecResidueField_apply]

abbrev scheme (n : ℕ) : Scheme := pullback π (locus R c L hz n).ι
abbrev projection (n : ℕ) : scheme R c L hz n ⟶ (locus R c L hz n).toScheme :=
  pullback.snd π (locus R c L hz n).ι
instance finite (n : ℕ) : IsFinite (projection R c L hz n) := inferInstance
instance flat (n : ℕ) : Flat (projection R c L hz n) := inferInstance
instance finitePresentation (n : ℕ) : LocallyOfFinitePresentation (projection R c L hz n) :=
  inferInstance

/-- On the actual degree-n stratum, the original restricted zero family
has constant degree n, with no value postulated for the original L. -/
lemma degree_eq (n : ℕ) (x : (locus R c L hz n).toScheme) :
    (projection R c L hz n).finrank x=n := by
  rw [degree_base_change]
  exact x.property
end ContactUniversalDegreeStrata318
