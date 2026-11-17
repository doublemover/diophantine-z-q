module
public import IntegerTensorFieldSquares318
public import OriginalIntegerReciprocalNormalization318
public section
noncomputable section
namespace OriginalIntegerRationalOverlapSquares318
open scoped TensorProduct
private theorem fieldCharZero (K F : Type*) [Field K] [Field F]
    [CharZero K] [Algebra K F] : CharZero F := by
  letI : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  exact Algebra.charZero_of_charZero K F

variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Finite := OriginalIntegerFiniteClosure318.Closure c
abbrev Infinity := OriginalIntegerReciprocalNormalization318.Closure c
abbrev Overlap := OriginalIntegerNormalizedOverlap318.Overlap c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance sourceCharZero : CharZero (L c) :=
  fieldCharZero (RatFunc ℚ) (L c)

@[expose] def finiteVal : Finite c →+* L c where
  toFun := fun z => z.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def finiteEmbedding : Finite c ⊗[ℤ] ℚ →+* L c :=
  IntegerTensorFieldSquares318.embedding (finiteVal c)

theorem finiteEmbedding_injective : Function.Injective (finiteEmbedding c) :=
  IntegerTensorFieldSquares318.embedding_injective (finiteVal c) Subtype.val_injective

@[expose] def infinityVal : Infinity c →+* L c where
  toFun := fun z => z.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def infinityEmbedding : Infinity c ⊗[ℤ] ℚ →+* L c :=
  IntegerTensorFieldSquares318.embedding (infinityVal c)

theorem infinityEmbedding_injective : Function.Injective (infinityEmbedding c) :=
  IntegerTensorFieldSquares318.embedding_injective (infinityVal c) Subtype.val_injective

@[expose] def overlapVal : Overlap c →+* L c where
  toFun := fun z => z.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def overlapEmbedding : Overlap c ⊗[ℤ] ℚ →+* L c :=
  IntegerTensorFieldSquares318.embedding (overlapVal c)

theorem overlapEmbedding_injective : Function.Injective (overlapEmbedding c) :=
  IntegerTensorFieldSquares318.embedding_injective (overlapVal c) Subtype.val_injective

/-- The literal coefficient-localized overlap maps, induced from the
already checked inclusions of the two integer closures into their SAME overlap. -/
@[expose] def fromFinite : Finite c ⊗[ℤ] ℚ →+* Overlap c ⊗[ℤ] ℚ :=
  IntegerTensorFieldSquares318.rationalMap
    (by
      letI := OriginalIntegerFiniteClosure318.baseAlgebra c
      letI := IntegralClosureAwayField318.fieldAlgebra (Polynomial.X : Polynomial ℤ)
        (OriginalIntegerNormalizedOverlap318.parameterUnit c)
      exact (OriginalIntegerNormalizedOverlap318.inclusion c).toRingHom)

@[expose] def fromInfinity : Infinity c ⊗[ℤ] ℚ →+* Overlap c ⊗[ℤ] ℚ :=
  IntegerTensorFieldSquares318.rationalMap
    (OriginalIntegerReciprocalNormalization318.inclusion c)

theorem finite_square : (overlapEmbedding c).comp (fromFinite c) = finiteEmbedding c := by
  apply IntegerTensorFieldSquares318.embedding_square
  ext z
  rfl

theorem infinity_square : (overlapEmbedding c).comp (fromInfinity c) = infinityEmbedding c := by
  apply IntegerTensorFieldSquares318.embedding_square
  ext z
  exact OriginalIntegerReciprocalNormalization318.inclusion_val c z

/-- Equality on this ACTUAL rational overlap can be checked in the specified
original Kummer field. This does not yet identify original-model section
restrictions or assert a global scheme isomorphism. -/
theorem overlap_equality_iff (z w : Overlap c ⊗[ℤ] ℚ) :
    z = w ↔ overlapEmbedding c z = overlapEmbedding c w :=
  (overlapEmbedding_injective c).eq_iff.symm

end OriginalIntegerRationalOverlapSquares318
