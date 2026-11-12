module
public import ActualOriginalCongruenceCircle318
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public section
noncomputable section
namespace ActualOriginalFiniteRationalArc318
open QuadricCRTAssembly318 ActualOriginalFiniteCircleIdentity318
open ActualOriginalCongruenceCircle318
open scoped BigOperators
set_option maxHeartbeats 16000000

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Exact rational-arc character factorization with the genuine standard
additive character modulo q. Coprimality is not needed for this identity. -/
lemma actual_rational_phase (q : ℕ) [NeZero q] (a n : ℤ) (β : ℝ) :
    fourier n (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar ((a*n : ℤ) : ZMod q) *
        fourier n (β : AddCircle (1 : ℝ)) := by
  rw [ZMod.stdAddChar_coe,fourier_coe_apply,fourier_coe_apply]
  simp only [Complex.ofReal_one,div_one,Complex.ofReal_add,
    Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast,Int.cast_mul]
  rw [←Complex.exp_add]
  congr 1
  ring

lemma actual_original_rational_phase (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (β : ℝ) (x : Coordinates ℤ) :
    fourier (equation κ x) (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar ((a : ZMod q) * equation (κ : ZMod q) (originalResidue q x)) *
        fourier (equation κ x) (β : AddCircle (1 : ℝ)) := by
  rw [actual_rational_phase,actual_original_residue_equation]
  simp only [Int.cast_mul]

/-- Literal q^5-residue decomposition of the ORIGINAL finite exponential
sum at a/q+β. Every fiber keeps its original points and weights. -/
theorem actual_original_rational_arc_decomposition (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (β : ℝ) (s : Finset (Coordinates ℤ)) (w : Coordinates ℤ → ℂ) :
    originalCircleSum κ s w (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ)) =
      ∑ r : Coordinates (ZMod q),
        ZMod.stdAddChar ((a : ZMod q) * equation (κ : ZMod q) r) *
          originalCircleSum κ (originalResidueSlice q r s) w
            (β : AddCircle (1 : ℝ)) := by
  classical
  have hpartition :
      (∑ r : Coordinates (ZMod q),
        ∑ x ∈ s.filter (fun x => originalResidue q x = r),
          w x * fourier (equation κ x)
            (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))) =
      originalCircleSum κ s w (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ)) := by
    simpa only [originalCircleSum,Finset.sum_apply] using
      (Finset.sum_fiberwise_of_maps_to
        (fun (x : Coordinates ℤ) (_ : x ∈ s) => Finset.mem_univ (originalResidue q x))
        (fun x => w x * fourier (equation κ x)
          (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))))
  rw [←hpartition]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [originalCircleSum,originalResidueSlice,Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hres := (Finset.mem_filter.mp hx).2
  rw [actual_original_rational_phase,hres]
  ring

theorem actual_original_number_of_residue_fibers (q : ℕ) [NeZero q] :
    Fintype.card (Coordinates (ZMod q)) = q^5 := by
  simp only [Coordinates,Fintype.card_prod,ZMod.card]
  ring

end ActualOriginalFiniteRationalArc318
