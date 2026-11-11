module
public import ContactGlobalSectionZero318
public import PrimeQuotientEmpty318
public section
namespace ContactGlobalZeroEmptyIdeals318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- Emptiness of the actual global zero scheme is detected by BOTH full
original chart ideals, not by a reduced locus or selected geometric points. -/
lemma iff_top : IsEmpty ↑(scheme R c L s) ↔
    finiteIdeal R c L s=⊤ ∧ infinityIdeal R c L s=⊤ := by
  constructor
  · intro h
    constructor
    · apply (PrimeQuotientEmpty318.iff_top _ _).mp
      exact ⟨fun z => h.false (finiteChart R c L s z)⟩
    · apply (PrimeQuotientEmpty318.iff_top _ _).mp
      exact ⟨fun z => h.false (infinityChart R c L s z)⟩
  · rintro ⟨hf,hi⟩
    have hF : IsEmpty ↑(finiteZero R c L s) := (PrimeQuotientEmpty318.iff_top _ _).mpr hf
    have hI : IsEmpty ↑(infinityZero R c L s) := (PrimeQuotientEmpty318.iff_top _ _).mpr hi
    refine ⟨fun z => ?_⟩
    rcases charts_cover R c L s z with ⟨a,ha⟩ | ⟨b,hb⟩
    · exact hF.false a
    · exact hI.false b
end ContactGlobalZeroEmptyIdeals318
