module
public import ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalAdditiveImageRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- Genuine additive map into the same actual function field. -/
def valueHom (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U] :
    Γ(originalRootIdealSheaf n i,U) →+ (originalCubicScheme n).functionField where
  toFun := ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U
  map_zero' := by
    simp only [ActualTwoDescentOriginalGlobalRationalValueRebuild318.value,
      ActualTwoDescentPushforwardRationalValueRebuild318.value,map_zero]
  map_add' := ActualTwoDescentPushforwardRationalValueRebuild318.add _ _ _ U

def image (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U] :
    AddSubgroup (originalCubicScheme n).functionField := (valueHom n i U).range

lemma mem_image (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U]
    (z : (originalCubicScheme n).functionField) : z ∈ image n i U ↔
      ∃ s : Γ(originalRootIdealSheaf n i,U),
        ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=z := Iff.rfl

/-- Restrictions preserve actual rational values, hence give literal
inclusions of additive images, not a new field identification. -/
lemma antitone (n : K) (i : Fin 3) (U V : (originalCubicScheme n).Opens)
    [Nonempty U] [Nonempty V] (h : V≤U) : image n i U ≤ image n i V := by
  intro z hz
  obtain ⟨s,rfl⟩ := (mem_image n i U z).mp hz
  exact (mem_image n i V _).mpr ⟨(originalRootIdealSheaf n i).presheaf.map (homOfLE h).op s,
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.restrict n i U V h s⟩

lemma scalar_closed (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (a : Γ(originalCubicScheme n,U)) (z : (originalCubicScheme n).functionField)
    (hz : z ∈ image n i U) :
    (originalCubicScheme n).germToFunctionField U a*z ∈ image n i U := by
  obtain ⟨s,rfl⟩ := (mem_image n i U z).mp hz
  exact (mem_image n i U _).mpr ⟨a • s,
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.scalar n i U a s⟩
end ActualTwoDescentOriginalRationalAdditiveImageRebuild318
