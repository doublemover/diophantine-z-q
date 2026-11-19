module
public import OriginalIntegerRationalGlobalRegularity318
public import OriginalIntegerRationalSourceIdentification318
public import OriginalIntegerRationalReciprocalChart318
public section
noncomputable section
namespace OriginalIntegerRationalTwoCover318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
abbrev Original := (ContactProjectiveModel318.coverMap c).normalization
abbrev FiniteRing := OriginalIntegerRationalNormalization318.IntegerClosure c
abbrev ReciprocalRing := OriginalIntegerReciprocalRationalNormalization318.IntegerClosure c

/-- The WHOLE finite and reciprocal chart embeddings constructed from the
integer rational tensor fibers jointly cover the ORIGINAL model. -/
theorem charts_cover (x : Original c) :
    (∃ y, OriginalIntegerRationalSourceIdentification318.rationalFiberChart c y = x) ∨
    (∃ y, OriginalIntegerRationalReciprocalChart318.fiberChart c y = x) := by
  obtain ⟨j, y, hy⟩ := (JLineAtlas318.cover ℚ).exists_eq
    ((ContactProjectiveModel318.coverMap c).fromNormalization x)
  have hj : j = 0 ∨ j = 1 := by omega
  have hmem : (ContactProjectiveModel318.coverMap c).fromNormalization x ∈
      JLineAtlas318.chart ℚ j ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact ⟨y, hy⟩
  rcases hj with rfl | rfl
  · right
    have hx : x ∈ (OriginalIntegerRationalReciprocalChart318.actualOpen c).1 := hmem
    rw [← OriginalIntegerRationalReciprocalChart318.fiberChart_range] at hx
    exact hx
  · left
    have hx : x ∈ (SourceGlobalAffine318.actualOpen c).1 := hmem
    rw [← OriginalIntegerRationalSourceIdentification318.rationalFiberChart_range] at hx
    exact hx

/-- Actual source schemes and actual maps, not just an assertion that two
abstract affine rings occur somewhere on the original model. -/
@[expose] def originalCover : (Original c).OpenCover where
  I₀ := Bool
  X i := if i then Spec (CommRingCat.of (ReciprocalRing c ⊗[ℤ] ℚ))
    else Spec (CommRingCat.of (FiniteRing c ⊗[ℤ] ℚ))
  f i := by
    cases i with
    | false => exact OriginalIntegerRationalSourceIdentification318.rationalFiberChart c
    | true => exact OriginalIntegerRationalReciprocalChart318.fiberChart c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      rcases charts_cover c x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    · intro i
      cases i <;> infer_instance

/-- The actual rational-base-change cover and actual original-model cover
have these specific objectwise isomorphisms. Gluing still requires equality
of the induced arrows on their overlap; no such equality is assumed here. -/
@[expose] def coverComponentIso (i : Bool) :
    (OriginalIntegerRationalGlobalRegularity318.rationalCover c).X i ≅
      (originalCover c).X i := by
  cases i with
  | false => exact OriginalIntegerRationalGlobalRegularity318.finiteFiberIso c
  | true => exact OriginalIntegerRationalGlobalRegularity318.reciprocalFiberIso c

end OriginalIntegerRationalTwoCover318
