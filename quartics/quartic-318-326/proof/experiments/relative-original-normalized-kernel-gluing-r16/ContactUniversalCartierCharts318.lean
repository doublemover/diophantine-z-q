module
public import ContactUniversalRegularIdeal318
public import OriginalRegularClosedCharts318
public import ContactGlobalZeroClosed318
public import ContactGeneratedLocalUniversalRegular318
public section
noncomputable section
namespace ContactUniversalCartierCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionParameter318 ContactOriginalCoefficientActions318
open ContactGeneratedLocalUniversalRegular318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "M" => generatedLine R c L
local instance : Module R Γ(M.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) M ⊤
local notation "S" => CommRingCat.of (parameterRing R c M)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
local notation "U" => universalLine R c M
local notation "s" => universalSection R c M (properties R c L).1

/-- The SAME global universal zero scheme of the internally constructed
positive original line has genuine Cartier charts: around every point of
the actual parameter curve it is the quotient by one non-zero-divisor,
with a Cartesian square. This is a total-family statement, NOT a claim
that every specialized section is regular or that the family is flat. -/
theorem regular_charts : OriginalRegularClosedCharts318.Property
    (ContactGlobalSectionZero318.into S c U s) := by
  intro x
  have hx : x ∈ (finiteInto S c).opensRange ⊔ (infinityInto S c).opensRange := by
    rw [ContactOriginalRelativePolynomialCharts318.cover]
    trivial
  rcases hx with ⟨a,ha⟩ | ⟨b,hb⟩
  · have h := OriginalRegularClosedCharts318.quotient
      (CommRingCat.of (S ⊗[ℚ] finiteRing c)) (ContactOriginalSectionZeros318.finiteIdeal S c U s)
      (ContactUniversalRegularIdeal318.finite_property R c M (properties R c L).1
        (properties R c L).2.1)
    obtain ⟨A,k,hk,⟨y,hy⟩,d,z,hz,hd⟩ := h a
    haveI : IsOpenImmersion k := hk
    refine ⟨A,k ≫ finiteInto S c,inferInstance,⟨y,?_⟩,d,
      z ≫ ContactGlobalSectionZero318.finiteChart S c U s,
      hz.paste_vert (ContactGlobalZeroChartSquares318.finite_square S c U s),hd⟩
    rw [Scheme.Hom.comp_apply,hy,ha]
  · have h := OriginalRegularClosedCharts318.quotient
      (CommRingCat.of (S ⊗[ℚ] infinityRing c)) (ContactOriginalSectionZeros318.infinityIdeal S c U s)
      (ContactUniversalRegularIdeal318.infinity_property R c M (properties R c L).1
        (properties R c L).2.2)
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
  ⟨inferInstance,regular_charts R c L⟩
end ContactUniversalCartierCharts318
