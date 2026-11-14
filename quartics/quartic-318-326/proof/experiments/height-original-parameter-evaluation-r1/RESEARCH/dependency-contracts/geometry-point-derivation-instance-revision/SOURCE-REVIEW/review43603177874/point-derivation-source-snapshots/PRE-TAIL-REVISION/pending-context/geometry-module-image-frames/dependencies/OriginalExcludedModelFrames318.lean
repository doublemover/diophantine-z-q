module
public import EmbeddedLatticeFrames318
public import OriginalCanonicalFiniteLattices318
public section
noncomputable section
namespace OriginalExcludedModelFrames318
open NumberField ActualFinitePlaceIntegers318 OriginalPointFinitePlaceRoots318
open OriginalExcludedPlaceData318 EmbeddedLatticeFrames318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)

/-- Remaining genuine model inputs at precisely the excluded places. The
embedded lattices, their free frames and containment of the ORIGINAL sections
are supplied, not proved to arise from a global model in this module. No Hodge
metric, KS image equality, degree equality or height conclusion is a field. -/
structure ModelFrames where
  model : (b : BadPlace c t) → Submodule (Integers b.val) (K c t)
  frame : (b : BadPlace c t) → Integers b.val ≃ₗ[Integers b.val] model b
  original_mem : ∀ (b : BadPlace c t) (n : Fin 2),
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈model b

variable (D : ModelFrames c t hn i)

/-- The formerly caller-supplied scalar generators are now extracted from
specified embedded model frames, without referring to a Hodge norm or KS target. -/
@[expose] def generators : ExcludedGenerators c t hn i where
  generator b := frameGenerator b.val (D.frame b)
  nonzero b := frameGenerator_ne b.val (D.frame b)
  original_mem b n := by
    rw [lattice_frameGenerator]
    exact D.original_mem b n

/-- At every excluded place the assembled canonical lattice is literally
the supplied model lattice. No abstract rank-one identification is substituted. -/
theorem assembled_bad (b : BadPlace c t) :
    OriginalCanonicalFiniteLattices318.modelLattice c t hn i
      (generators c t hn i D) b.val=D.model b := by
  rw [OriginalCanonicalFiniteLattices318.modelLattice_bad c t hn i
    (generators c t hn i D) b.val b.property]
  exact lattice_frameGenerator b.val (D.frame b)

/-- At every good place, the actual previously constructed cotangent lattice
is retained unchanged, independently of the excluded-place model inputs. -/
theorem assembled_good (w : FinitePlace (K c t))
    (hw : w (ContactArithmeticDenominator318.denominator c : K c t)=1) :
    OriginalCanonicalFiniteLattices318.modelLattice c t hn i
      (generators c t hn i D) w=OriginalGoodCotangentLattice318.modelLattice c t hn w hw i :=
  OriginalCanonicalFiniteLattices318.modelLattice_good c t hn i (generators c t hn i D) w hw
end OriginalExcludedModelFrames318
