module
public import ActualOriginalPositiveGraphIntegral318
public section
noncomputable section
namespace ActualOriginalGraphMassNormalization318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalArchimedeanChartInput318
open ActualOriginalPositiveGraphIntegral318 MeasureTheory ActualOriginalRealGoodRegion318
open scoped ContDiff
set_option maxHeartbeats 16000000

@[expose] def normalizedWeight (κ : ℝ) (W : Coordinates ℝ→ℝ) : Coordinates ℝ→ℝ :=
  fun x => W x/graphMass κ W
lemma actual_density_div (κ c : ℝ) (W : Coordinates ℝ→ℝ) :
    graphDensity κ (fun x => W x/c)=fun v => graphDensity κ W v/c := by
  funext v
  simp only [graphDensity,div_eq_mul_inv]
  ring
lemma actual_mass_div (κ c : ℝ) (W : Coordinates ℝ→ℝ) :
    graphMass κ (fun x => W x/c)=graphMass κ W/c := by
  unfold graphMass
  rw [actual_density_div]
  exact integral_div c (graphDensity κ W)
lemma actual_normalized_mass (κ : ℝ) (W : Coordinates ℝ→ℝ) (hW : 0<graphMass κ W) :
    graphMass κ (normalizedWeight κ W)=1 := by
  rw [normalizedWeight,actual_mass_div]
  exact div_self (ne_of_gt hW)
lemma actual_normalized_support (κ : ℝ) (W : Coordinates ℝ→ℝ) (hW : 0<graphMass κ W) :
    tsupport (normalizedWeight κ W)=tsupport W := by
  have he : Function.support (normalizedWeight κ W)=Function.support W := by
    ext x
    change W x/graphMass κ W≠0 ↔ W x≠0
    constructor
    · intro hh hz
      exact hh (by rw [hz,zero_div])
    · intro hh
      exact div_ne_zero hh (ne_of_gt hW)
  exact congrArg closure he

/-- Normalization of the SAME actual graph integral preserves its whole
original good support and derivative bound. The resulting graph mass is
exactly1; this does not identify an oscillatory singular-integral convention. -/
theorem actual_original_normalized_graph_weight {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀y,0≤W y) ∧ 0<W x ∧
      (∀y∈tsupport W,y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) ∧
      Integrable (graphDensity κ W) ∧ graphMass κ W=1 := by
  obtain ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWb,hWx,hWs,hInt,hMass⟩ :=
    actual_original_positive_graph_integral κ hκ γ
  have hsupport := actual_normalized_support κ W hMass
  have hc : HasCompactSupport (normalizedWeight κ W) := by
    change IsCompact (tsupport (normalizedWeight κ W))
    rw [hsupport]
    exact hWc
  have hd : ContDiff ℝ ∞ (normalizedWeight κ W) := hWd.div_const _
  have hi : Integrable (graphDensity κ (normalizedWeight κ W)) := by
    rw [normalizedWeight,actual_density_div]
    exact hInt.div_const _
  refine ⟨x,normalizedWeight κ W,η,hQ,ha,hη,hc,hd,?_,?_,?_,hi,actual_normalized_mass κ W hMass⟩
  · intro y
    exact div_nonneg (hWb y).1 hMass.le
  · change 0<W x/graphMass κ W
    rw [hWx]
    exact div_pos (by norm_num) hMass
  · intro y hy
    rw [hsupport] at hy
    exact hWs y hy

end ActualOriginalGraphMassNormalization318
