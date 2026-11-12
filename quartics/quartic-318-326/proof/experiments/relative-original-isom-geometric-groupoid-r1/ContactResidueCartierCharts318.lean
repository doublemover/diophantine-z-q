module
public import ContactResidueSectionRegular318
public import OriginalRegularSectionIdeal318
public import OriginalRegularClosedCharts318
public import ContactGlobalZeroClosed318
public import ContactGeneratedLocalUniversalRegular318
public section
noncomputable section
namespace ContactResidueCartierCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionParameter318 ContactOriginalCoefficientActions318
open ContactGeneratedLocalUniversalRegular318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (s : Γ(L.object,⊤))
  (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s)
local notation "S" => R
local notation "U" => L

/-- The original section with genuinely nonzero residue fibers has
actual Cartier quotient charts over its WHOLE coefficient ring. The two
original affine charts and their original zero Cartesian squares glue
these regular equations without a positivity/global-generation premise. -/
theorem regular_charts : OriginalRegularClosedCharts318.Property
    (ContactGlobalSectionZero318.into S c U s) := by
  intro x
  have hx : x ∈ (finiteInto S c).opensRange ⊔ (infinityInto S c).opensRange := by
    rw [ContactOriginalRelativePolynomialCharts318.cover]
    trivial
  rcases hx with ⟨a,ha⟩ | ⟨b,hb⟩
  · have h := OriginalRegularClosedCharts318.quotient
      (CommRingCat.of (S ⊗[ℚ] finiteRing c)) (ContactOriginalSectionZeros318.finiteIdeal S c U s)
      (OriginalRegularSectionIdeal318.property (CommRingCat.of (R ⊗[ℚ] finiteRing c))
        (LineSheafPullback318.line (finiteInto R c) L) _
        (ContactResidueSectionRegular318.finite_regular R c L s hs))
    obtain ⟨A,k,hk,⟨y,hy⟩,d,z,hz,hd⟩ := h a
    haveI : IsOpenImmersion k := hk
    refine ⟨A,k ≫ finiteInto S c,inferInstance,⟨y,?_⟩,d,
      z ≫ ContactGlobalSectionZero318.finiteChart S c U s,
      hz.paste_vert (ContactGlobalZeroChartSquares318.finite_square S c U s),hd⟩
    rw [Scheme.Hom.comp_apply,hy,ha]
  · have h := OriginalRegularClosedCharts318.quotient
      (CommRingCat.of (S ⊗[ℚ] infinityRing c)) (ContactOriginalSectionZeros318.infinityIdeal S c U s)
      (OriginalRegularSectionIdeal318.property (CommRingCat.of (R ⊗[ℚ] infinityRing c))
        (LineSheafPullback318.line (infinityInto R c) L) _
        (ContactResidueSectionRegular318.infinity_regular R c L s hs))
    obtain ⟨A,k,hk,⟨y,hy⟩,d,z,hz,hd⟩ := h b
    haveI : IsOpenImmersion k := hk
    refine ⟨A,k ≫ infinityInto S c,inferInstance,⟨y,?_⟩,d,
      z ≫ ContactGlobalSectionZero318.infinityChart S c U s,
      hz.paste_vert (ContactGlobalZeroChartSquares318.infinity_square S c U s),hd⟩
    rw [Scheme.Hom.comp_apply,hy,hb]

/-- Full scheme-theoretic criterion including closedness of the actual
original universal zero immersion. Nilpotent structure is unchanged. -/
theorem closed_and_regular_charts :
    IsClosedImmersion (ContactGlobalSectionZero318.into S c U s) ∧
    OriginalRegularClosedCharts318.Property (ContactGlobalSectionZero318.into S c U s) :=
  ⟨inferInstance,regular_charts R c L s hs⟩
end ContactResidueCartierCharts318
