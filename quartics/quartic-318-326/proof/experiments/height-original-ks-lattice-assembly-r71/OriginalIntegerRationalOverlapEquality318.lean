module
public import OriginalIntegerRationalGenericPoint318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace OriginalIntegerRationalOverlapEquality318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
universe u

private theorem dominant_of_injective {R F : Type u} [CommRing R] [CommRing F]
    (h : R →+* F) (hh : Function.Injective h) :
    IsDominant (Spec.map (CommRingCat.ofHom h)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap h)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical h).mpr
  rw [(RingHom.injective_iff_ker_eq_bot).mp hh]
  exact bot_le

variable (c : Fin 4 → ℚˣ)
open OriginalIntegerRationalOverlapSquares318
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

local instance originalSeparated : (ContactProjectiveModel318.model c).IsSeparated := by
  letI := (ContactGlobalProper318.proper_integral_extension c).2.2
  refine ⟨?_⟩
  have hs : IsSeparated
      ((ContactProjectiveModel318.modelMap c ≫ ProjectiveJLine318.structureMap ℚ) ≫
        terminal.from (Spec (CommRingCat.of ℚ))) := inferInstance
  simpa only [terminal.comp_from] using hs

/-- Actual arrows from the literal coefficient-localized common overlap
into the original model agree. The proof uses the proved same-field squares,
the canonical original normalization point, injectivity/reducedness of the
actual overlap, and native separated-target dominant extensionality. -/
theorem actual_overlap_equality :
    Spec.map (CommRingCat.ofHom (fromFinite c)) ≫
      OriginalIntegerRationalSourceIdentification318.rationalFiberChart c =
    Spec.map (CommRingCat.ofHom (fromInfinity c)) ≫
      OriginalIntegerRationalReciprocalChart318.fiberChart c := by
  letI : _root_.IsReduced (Overlap c ⊗[ℤ] ℚ) :=
    isReduced_of_injective (overlapEmbedding c) (overlapEmbedding_injective c)
  letI : IsDominant (Spec.map (CommRingCat.ofHom (overlapEmbedding c))) :=
    dominant_of_injective (overlapEmbedding c) (overlapEmbedding_injective c)
  apply ext_of_isDominant (Spec.map (CommRingCat.ofHom (overlapEmbedding c)))
  calc
    Spec.map (CommRingCat.ofHom (overlapEmbedding c)) ≫
        (Spec.map (CommRingCat.ofHom (fromFinite c)) ≫
          OriginalIntegerRationalSourceIdentification318.rationalFiberChart c) =
      Spec.map (CommRingCat.ofHom (finiteEmbedding c)) ≫
        OriginalIntegerRationalSourceIdentification318.rationalFiberChart c := by
          rw [← Category.assoc, ← Spec.map_comp]
          change Spec.map (CommRingCat.ofHom ((overlapEmbedding c).comp (fromFinite c))) ≫ _ = _
          rw [finite_square]
    _ = OriginalIntegerRationalGenericPoint318.canonicalPoint c :=
      OriginalIntegerRationalGenericPoint318.finite_tensor_point c
    _ = Spec.map (CommRingCat.ofHom (infinityEmbedding c)) ≫
        OriginalIntegerRationalReciprocalChart318.fiberChart c :=
      (OriginalIntegerRationalGenericPoint318.reciprocal_tensor_point c).symm
    _ = Spec.map (CommRingCat.ofHom (overlapEmbedding c)) ≫
        (Spec.map (CommRingCat.ofHom (fromInfinity c)) ≫
          OriginalIntegerRationalReciprocalChart318.fiberChart c) := by
          rw [← Category.assoc, ← Spec.map_comp]
          change _ = Spec.map (CommRingCat.ofHom ((overlapEmbedding c).comp (fromInfinity c))) ≫ _
          rw [infinity_square]

end OriginalIntegerRationalOverlapEquality318
