module
public import ActualOriginalPositiveRealPoint318
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public section
noncomputable section
namespace ActualOriginalRealGoodRegion318
open QuadricCRTAssembly318 ActualOriginalPositiveRealPoint318
open scoped Topology
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J]

@[expose] def region (γ : J→ℝ) : Set (Coordinates ℝ) :=
  {x | 0<x.1.1 ∧ 0<x.2.1.1 ∧ 0<x.2.2 ∧ ∀j,0<originalForm (γ j) x}
lemma originalForm_continuous (γ : ℝ) : Continuous (originalForm γ) := by
  unfold originalForm
  fun_prop
lemma original_equation_continuous (κ : ℝ) : Continuous (equation κ : Coordinates ℝ→ℝ) := by
  unfold equation
  fun_prop
lemma region_open (γ : J→ℝ) : IsOpen (region γ) := by
  have ha : IsOpen {x : Coordinates ℝ | 0<x.1.1} := isOpen_lt continuous_const (by fun_prop)
  have hc : IsOpen {x : Coordinates ℝ | 0<x.2.1.1} := isOpen_lt continuous_const (by fun_prop)
  have hw : IsOpen {x : Coordinates ℝ | 0<x.2.2} := isOpen_lt continuous_const (by fun_prop)
  have hf : IsOpen {x : Coordinates ℝ | ∀j,0<originalForm (γ j) x} := by
    have he : {x : Coordinates ℝ | ∀j,0<originalForm (γ j) x}=
        ⋂j,{x : Coordinates ℝ | 0<originalForm (γ j) x} := by ext x;simp
    rw [he]
    exact isOpen_iInter (fun j => isOpen_lt continuous_const (originalForm_continuous (γ j)))
  exact ha.inter (hc.inter (hw.inter hf))

/-- The whole support can be kept uniformly away from the zero first
normal derivative; the lower threshold is chosen from the actual point. -/
@[expose] def protectedRegion (γ : J→ℝ) (x : Coordinates ℝ) : Set (Coordinates ℝ) :=
  region γ ∩ {y | x.1.1/2<y.1.1}
lemma protectedRegion_open (γ : J→ℝ) (x : Coordinates ℝ) :
    IsOpen (protectedRegion γ x) :=
  (region_open γ).inter (isOpen_lt continuous_const (by fun_prop))
lemma self_mem_protected (γ : J→ℝ) (x : Coordinates ℝ) (hx : x∈region γ) :
    x∈protectedRegion γ x := by
  exact ⟨hx,by linarith [hx.1]⟩
lemma actual_gradient_lower (κ : ℝ) (γ : J→ℝ) (x y : Coordinates ℝ)
    (hy : y∈protectedRegion γ x) :
    x.1.1<ActualQuadricTaylor318.gradient κ y 0 := by
  change x.1.1<2*y.1.1
  linarith [hy.2]

end ActualOriginalRealGoodRegion318
