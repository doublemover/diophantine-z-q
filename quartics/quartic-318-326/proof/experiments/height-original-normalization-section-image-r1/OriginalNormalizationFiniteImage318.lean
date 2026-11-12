module
public import OriginalNormalizationIntegralEvaluation318
public section
noncomputable section
namespace OriginalNormalizationFiniteImage318
open NumberField ActualFinitePlaceIntegers318
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationDifferentValue318 OriginalNormalizationConductorSpecialization318
open OriginalNormalizationIntegralEvaluation318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "F" => K c t
local notation "C" => conductorValues c t w D M
local notation "L" => codifferentValues c t w D M
local notation "δ" => differentValue c t w D M

@[expose] def integralPreimage : Submodule R R := C.comap (Algebra.linearMap R F)
@[expose] def integralImageMap : integralPreimage c t w D M →ₗ[R] C :=
  ((Algebra.linearMap R F).comp (integralPreimage c t w D M).subtype).codRestrict C
    (fun x => x.property)

variable (ht : w (t : F) ≤ 1)
include ht in
lemma integralImageMap_surjective : Function.Surjective (integralImageMap c t w D M) := by
  intro y
  let r : R := ⟨y.val,(bounded_iff w _).mp
    (conductorValues_bounded c t w D M ht y.val y.property)⟩
  refine ⟨⟨r,?_⟩,?_⟩
  · exact y.property
  · exact Subtype.ext rfl

include ht in
/-- The actual conductor value image is finite on the genuine integral
finite-coordinate branch. It is the image of its exact integral preimage. -/
lemma finite_conductorValues : Module.Finite R C := by
  letI : Module.Finite R (integralPreimage c t w D M) := inferInstance
  exact Module.Finite.of_surjective (integralImageMap c t w D M)
    (integralImageMap_surjective c t w D M ht)

/-- Exact multiplication by the SAME evaluated inverse raw different,
from the actual conductor image onto the actual normalized codifferent image. -/
@[expose] def inverseDifferentMap : C →ₗ[R] L :=
  ((FinitePlaceMultiplicativeDual318.multiply w δ⁻¹).comp C.subtype).codRestrict L
    (fun x => (mem_iff_inverse c t w D M _).mpr ⟨x.val,x.property,rfl⟩)
lemma inverseDifferentMap_surjective : Function.Surjective (inverseDifferentMap c t w D M) := by
  intro z
  obtain ⟨y,hy,hz⟩ := (mem_iff_inverse c t w D M z.val).mp z.property
  exact ⟨⟨y,hy⟩,Subtype.ext hz.symm⟩

include ht in
/-- A genuine nonzero finite V-lattice of normalized-codifferent values
has now been produced on this actual branch, not assumed from field rank. -/
lemma finite_codifferentValues : Module.Finite R L := by
  letI : Module.Finite R C := finite_conductorValues c t w D M ht
  exact Module.Finite.of_surjective (inverseDifferentMap c t w D M)
    (inverseDifferentMap_surjective c t w D M)
end OriginalNormalizationFiniteImage318
