module
public import OriginalIntegerRationalOverlapSquares318
public import OriginalIntegerRationalSourceIdentification318
public import OriginalIntegerRationalReciprocalChart318
public section
noncomputable section
namespace OriginalIntegerRationalChartFieldSquares318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
open OriginalIntegerRationalOverlapSquares318
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance sourceCharZero : CharZero (L c) :=
  Algebra.charZero_of_charZero (RatFunc ℚ) (L c)
attribute [local instance] OriginalIntegerRationalNormalization318.rationalizationAlgebra
attribute [local instance] OriginalIntegerReciprocalRationalNormalization318.rationalizationAlgebra

/-- The finite whole-chart identification induces precisely the same map
into the original L as integer coefficient rationalization. -/
theorem finite_chart_field_square :
    (ContactKummerOrder318.embedding c).comp
      (OriginalIntegerRationalSourceIdentification318.integerRationalFiberOrderEquiv c).toRingHom =
    finiteEmbedding c := by
  apply IsLocalization.ringHom_ext (IntegerTensorFieldSquares318.denominators (Finite c))
  ext z
  change ContactKummerOrder318.embedding c
    (OriginalIntegerRationalSourceIdentification318.rationalOrderEquiv c
      (OriginalIntegerRationalNormalization318.integerRationalFiberEquiv c
        (algebraMap (Finite c) (Finite c ⊗[ℤ] ℚ) z))) =
    finiteEmbedding c (algebraMap (Finite c) (Finite c ⊗[ℤ] ℚ) z)
  rw [AlgEquiv.commutes,
    OriginalIntegerRationalSourceIdentification318.rationalOrderEquiv_embedding,
    IntegerTensorFieldSquares318.embedding_base]
  rfl

@[expose] def originalReciprocalVal :
    OriginalIntegerRationalReciprocalChart318.OriginalClosure c →+*
      OriginalIntegerRationalReciprocalChart318.OriginalOpenOrder c where
  toFun := fun z => z.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original reciprocal normalization section ring has this specified
embedding, inherited through its normal OpenOrder, not an arbitrary field iso. -/
@[expose] def reciprocalSectionsField :
    OriginalIntegerRationalReciprocalChart318.chartRing c →+* L c :=
  (SourceOpenFractionField318.openEmbedding c).comp
    ((originalReciprocalVal c).comp
      (OriginalIntegerRationalReciprocalChart318.sectionsEquiv c).toRingHom)

/-- Whole reciprocal-chart sections also have the very same original-field
map as the coefficient-localized reciprocal integer closure. -/
theorem reciprocal_chart_field_square :
    (reciprocalSectionsField c).comp
      (OriginalIntegerRationalReciprocalChart318.fiberSectionsEquiv c).toRingHom =
    infinityEmbedding c := by
  apply IsLocalization.ringHom_ext (IntegerTensorFieldSquares318.denominators (Infinity c))
  ext z
  change SourceOpenFractionField318.openEmbedding c
    ((OriginalIntegerRationalReciprocalChart318.sectionsEquiv c)
      ((OriginalIntegerRationalReciprocalChart318.sectionsEquiv c).symm
        (OriginalIntegerRationalReciprocalChart318.rationalClosureEquiv c
          (OriginalIntegerReciprocalRationalNormalization318.integerRationalFiberEquiv c
            (algebraMap (Infinity c) (Infinity c ⊗[ℤ] ℚ) z))))).val =
    infinityEmbedding c (algebraMap (Infinity c) (Infinity c ⊗[ℤ] ℚ) z)
  rw [RingEquiv.apply_symm_apply, AlgEquiv.commutes,
    OriginalIntegerRationalReciprocalChart318.rationalClosureEquiv_embedding,
    IntegerTensorFieldSquares318.embedding_base]
  rfl

end OriginalIntegerRationalChartFieldSquares318
