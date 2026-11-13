module
public import OriginalNormalChartRanges318
public section
noncomputable section
namespace OriginalNormalTwoChartCover318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)

/-- Joint surjectivity of the two OLD whole normal-order charts of the
SAME M. The base point can be arbitrary; no genericity premise is used. -/
theorem covers (x : M.scheme) :
    (∃ y, OriginalNormalOrderChart318.chart c t w D M y=x) ∨
    (∃ y, OriginalNormalInfinityChart318.chart c t w D M y=x) := by
  have hx : M.projection x ∈ (⊤ : (ProjectiveJLine318.scheme (V c t w)).Opens) := trivial
  rw [←JLineAtlas318.standard_opens_cover (V c t w)] at hx
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [←JLineAtlas318.chart_range,←Scheme.Hom.image_top_eq_opensRange] at hi
  fin_cases i
  · right
    change x ∈ (OriginalNormalInfinityChart318.chart c t w D M).opensRange
    rw [OriginalNormalChartRanges318.infinity_range]
    exact hi
  · left
    change x ∈ (OriginalNormalOrderChart318.chart c t w D M).opensRange
    rw [OriginalNormalChartRanges318.finite_range]
    exact hi

/-- Actual open-cover data with the previously constructed chart maps. -/
@[expose] def cover : M.scheme.OpenCover where
  I₀ := Fin 2
  X i := if i=0 then Spec (CommRingCat.of (OriginalNormalInfinityOrder318.Order c t w D))
    else Spec (CommRingCat.of (OriginalNormalOrderChart318.Order c t w D))
  f i := if h : i=0 then by subst i; exact OriginalNormalInfinityChart318.chart c t w D M
    else by simpa only [h,if_false] using OriginalNormalOrderChart318.chart c t w D M
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases covers c t w D M x with ⟨y,hy⟩ | ⟨y,hy⟩
      · exact ⟨1,y,hy⟩
      · exact ⟨0,y,hy⟩
    · intro i
      fin_cases i <;> dsimp <;> infer_instance

/-- In particular the existing valuative center lands in the cover.
This does not assert that its whole valuation-ring morphism lies in a
single chart, or that the normal model is regular. -/
theorem center_covered (x : Spec (CommRingCat.of (V c t w))) :
    (∃ y, OriginalNormalOrderChart318.chart c t w D M y=M.center x) ∨
    (∃ y, OriginalNormalInfinityChart318.chart c t w D M y=M.center x) :=
  covers c t w D M (M.center x)
end OriginalNormalTwoChartCover318
