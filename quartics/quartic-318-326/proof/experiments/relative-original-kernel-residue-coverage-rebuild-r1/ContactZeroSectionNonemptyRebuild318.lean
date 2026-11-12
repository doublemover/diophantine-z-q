module
public import ContactGlobalZeroEmptyIdeals318
public import SourceScalarExtension318
public section
noncomputable section
namespace ContactZeroSectionNonemptyRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
/-- The entire original finite zero ideal of the zero section vanishes.
This uses the actual coefficient restriction, not just residue support. -/
lemma finite_zero : finiteIdeal R c L 0 = ⊥ := by
  unfold finiteIdeal OriginalAffineSectionZero318.ideal
  have hz : finiteSection R c L 0 = 0 := by
    change (ContactRelativeOriginalHZero318.pair R c L 0).1 = 0
    rw [map_zero]
    rfl
  rw [hz]
  apply le_antisymm _ bot_le
  rintro x ⟨φ,rfl⟩
  exact map_zero φ
/-- Over every coefficient field the original finite chart is nonempty,
so the zero section cannot have an empty whole zero scheme. -/
theorem nonzero_of_empty (K : CommRingCat.{0}) [Field K] [Algebra ℚ K]
    (c : Fin 4 → ℚˣ) (N : Line (curve K c)) (s : Γ(N.object,⊤))
    (hs : IsEmpty ↑(ContactGlobalSectionZero318.scheme K c N s)) : s ≠ 0 := by
  letI : CharZero K := algebraRat.charZero K
  letI : IsDomain (K ⊗[ℚ] finiteRing c) := SourceScalarExtension318.scalarExtension_domain K c
  intro h
  have ht := ((ContactGlobalZeroEmptyIdeals318.iff_top K c N s).mp hs).1
  rw [h,finite_zero] at ht
  exact bot_ne_top ht
end ContactZeroSectionNonemptyRebuild318
