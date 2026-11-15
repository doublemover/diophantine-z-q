module
public import FiniteModuleImageFrame318
public import OriginalFiniteModelFrames318
public section
noncomputable section
namespace OriginalFiniteImageModels318
open NumberField ActualFinitePlaceIntegers318 OriginalPointFinitePlaceRoots318
open OriginalExcludedPlaceData318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (E : BadPlace c t → Type*) [∀ b, AddCommGroup (E b)]
  [∀ b, Module (Integers b.val) (E b)] [∀ b, Module.Finite (Integers b.val) (E b)]

/-- Genuine integral modules and their evaluation are still supplied. The
lattice, its finite generation and free frame are NOT supplied. Lifts must
evaluate to both exact original sections, not an alternative pair. -/
structure EvaluationData where
  evaluation : (b : BadPlace c t) → E b →ₗ[Integers b.val] K c t
  originalSection : (b : BadPlace c t) → Fin 2 → E b
  section_value : ∀ (b : BadPlace c t) (n : Fin 2),
    evaluation b (originalSection b n)=
      (![ContactBicanonicalPointHeight318.a0 c t hn i,
        ContactBicanonicalPointHeight318.a1 c t hn i] n)

variable (D : EvaluationData c t hn i E)

/-- Construct the prior finite-model input from actual module images. Whether
these are canonical/dualizing images of the correct model remains a geometric
identification obligation, not a consequence of finite generation. -/
@[expose] def finiteModels : OriginalFiniteModelFrames318.FiniteModels c t hn i where
  model b := FiniteModuleImageFrame318.image b.val (E b) (D.evaluation b)
  finite_generation b := FiniteModuleImageFrame318.image_fg b.val (E b) (D.evaluation b)
  original_mem b n := ⟨D.originalSection b n,D.section_value b n⟩

@[expose] def modelFrames : OriginalExcludedModelFrames318.ModelFrames c t hn i :=
  OriginalFiniteModelFrames318.modelFrames c t hn i (finiteModels c t hn i E D)

/-- The downstream bad-place lattice is exactly the evaluation image, not
merely abstractly isomorphic to it. All existing good-place lattices stay fixed. -/
theorem assembled_bad (b : BadPlace c t) :
    OriginalCanonicalFiniteLattices318.modelLattice c t hn i
      (OriginalExcludedModelFrames318.generators c t hn i (modelFrames c t hn i E D)) b.val=
        (D.evaluation b).range :=
  OriginalFiniteModelFrames318.assembled_bad c t hn i (finiteModels c t hn i E D) b
end OriginalFiniteImageModels318
