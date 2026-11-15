module
public import FiniteGeneratedPlaceFrame318
public import OriginalExcludedModelFrames318
public section
noncomputable section
namespace OriginalFiniteModelFrames318
open NumberField ActualFinitePlaceIntegers318 OriginalPointFinitePlaceRoots318
open OriginalExcludedPlaceData318 OriginalExcludedModelFrames318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)

/-- Residual model input with NO free-frame or rank premise. Actual geometric
model existence and finite generation are still supplied; neither is asserted
here to follow from an unconstructed global bad-prime model. -/
structure FiniteModels where
  model : (b : BadPlace c t) → Submodule (Integers b.val) (K c t)
  finite_generation : ∀ b, (model b).FG
  original_mem : ∀ (b : BadPlace c t) (n : Fin 2),
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈model b

variable (D : FiniteModels c t hn i)

/-- The already-defined ModelFrames input is now produced from finite model
submodules. Nontriviality comes from the actual nonzero original a0; no zero
module or missing-place case is discarded. -/
@[expose] def modelFrames : ModelFrames c t hn i where
  model := D.model
  frame b := FiniteGeneratedPlaceFrame318.frame b.val (D.model b) (D.finite_generation b)
    (ContactBicanonicalPointHeight318.a0 c t hn i) (D.original_mem b 0)
    (ContactBicanonicalPointHeight318.a0_ne c t hn i)
  original_mem := D.original_mem

/-- The bad-place lattice passed downstream remains exactly the supplied
geometric model; selecting a free frame does not replace that submodule. -/
theorem assembled_bad (b : BadPlace c t) :
    OriginalCanonicalFiniteLattices318.modelLattice c t hn i
      (OriginalExcludedModelFrames318.generators c t hn i (modelFrames c t hn i D)) b.val=D.model b :=
  OriginalExcludedModelFrames318.assembled_bad c t hn i (modelFrames c t hn i D) b
end OriginalFiniteModelFrames318
