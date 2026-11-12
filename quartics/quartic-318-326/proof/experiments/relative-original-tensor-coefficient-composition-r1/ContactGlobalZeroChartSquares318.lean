module
public import ContactGlobalSectionZero318
public import ContactOriginalOverlapRanges318
public import QuotientOpenRange318
public section
noncomputable section
namespace ContactGlobalZeroChartSquares318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionZeros318 ContactGlobalSectionZero318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

lemma finite_preimage : (ContactGlobalSectionZero318.into R c L s) ⁻¹ᵁ
    (finiteInto R c).opensRange = (finiteChart R c L s).opensRange := by
  ext x
  constructor
  · intro hx
    rcases charts_cover R c L s x with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨a,rfl⟩
    · have hb : b ∈ (toInfinity R c L s).opensRange := by
        rw [show (toInfinity R c L s).opensRange =
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) ⁻¹ᵁ
          (ContactOriginalRelativeOverlap318.infinityEdge R c).opensRange from
            QuotientOpenRange318.range (infinityArrow R c) _ _ (infinity_overlap R c L s)]
        rw [ContactOriginalOverlapRanges318.infinity_edge_range]
        change (infinityIntoOriginal R c L s) b ∈ (finiteInto R c).opensRange
        change (ContactGlobalSectionZero318.into R c L s) (infinityChart R c L s b) ∈ _ at hx
        rw [← Scheme.Hom.comp_apply,infinityChart_into] at hx
        exact hx
      obtain ⟨z,hz⟩ := hb
      refine ⟨toFinite R c L s z,?_⟩
      change (toFinite R c L s ≫ finiteChart R c L s) z = _
      rw [pushout.condition]
      change infinityChart R c L s (toInfinity R c L s z) = _
      rw [hz]
  · rintro ⟨a,rfl⟩
    change (ContactGlobalSectionZero318.into R c L s) (finiteChart R c L s a) ∈ _
    rw [← Scheme.Hom.comp_apply,finiteChart_into]
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s))) a,rfl⟩

lemma infinity_preimage : (ContactGlobalSectionZero318.into R c L s) ⁻¹ᵁ
    (infinityInto R c).opensRange = (infinityChart R c L s).opensRange := by
  ext x
  constructor
  · intro hx
    rcases charts_cover R c L s x with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · have ha : a ∈ (toFinite R c L s).opensRange := by
        rw [show (toFinite R c L s).opensRange =
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) ⁻¹ᵁ
          (ContactOriginalRelativeOverlap318.finiteEdge R c).opensRange from
            QuotientOpenRange318.range (finiteArrow R c) _ _ (finite_overlap R c L s)]
        rw [ContactOriginalOverlapRanges318.finite_edge_range]
        change (finiteIntoOriginal R c L s) a ∈ (infinityInto R c).opensRange
        change (ContactGlobalSectionZero318.into R c L s) (finiteChart R c L s a) ∈ _ at hx
        rw [← Scheme.Hom.comp_apply,finiteChart_into] at hx
        exact hx
      obtain ⟨z,hz⟩ := ha
      refine ⟨toInfinity R c L s z,?_⟩
      change (toInfinity R c L s ≫ infinityChart R c L s) z = _
      rw [← pushout.condition]
      change finiteChart R c L s (toFinite R c L s z) = _
      rw [hz]
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    change (ContactGlobalSectionZero318.into R c L s) (infinityChart R c L s b) ∈ _
    rw [← Scheme.Hom.comp_apply,infinityChart_into]
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s))) b,rfl⟩

/-- The entire inverse image of each original chart is its original zero
quotient, as a categorical pullback and not just a matching set of points. -/
lemma finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s))))
    (finiteChart R c L s) (finiteInto R c) (ContactGlobalSectionZero318.into R c L s) :=
  IsOpenImmersion.isPullback _ _ _ _ (finiteChart_into R c L s) (finite_preimage R c L s)
lemma infinity_square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s))))
    (infinityChart R c L s) (infinityInto R c) (ContactGlobalSectionZero318.into R c L s) :=
  IsOpenImmersion.isPullback _ _ _ _ (infinityChart_into R c L s) (infinity_preimage R c L s)
end ContactGlobalZeroChartSquares318
