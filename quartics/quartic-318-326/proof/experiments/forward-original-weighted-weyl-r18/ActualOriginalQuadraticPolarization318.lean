module
public import ActualOriginalCircleMinorArcIdentity318
public section
noncomputable section
namespace ActualOriginalQuadraticPolarization318
open QuadricCRTAssembly318
open scoped BigOperators

/-- The integral bilinear form of the ORIGINAL five-variable quadric.
The coefficient -kappa and both negative unit entries are retained. -/
@[expose] def originalBilinear (κ : ℤ) (h y : Coordinates ℤ) : ℤ :=
  h.1.1*y.1.1+h.1.2*y.1.2-
    (h.2.1.1*y.2.1.1+h.2.1.2*y.2.1.2)-κ*h.2.2*y.2.2

lemma actual_original_polarization (κ : ℤ) (h y : Coordinates ℤ) :
    equation κ (h+y)-equation κ y = equation κ h+2*originalBilinear κ h y := by
  rcases h with ⟨⟨a,b⟩,⟨c,d⟩,e⟩
  rcases y with ⟨⟨f,g⟩,⟨i,j⟩,k⟩
  change (a+f)^2+(b+g)^2-((c+i)^2+(d+j)^2)-κ*(e+k)^2-
    (f^2+g^2-(i^2+j^2)-κ*k^2)=
    a^2+b^2-(c^2+d^2)-κ*e^2+2*(a*f+b*g-(c*i+d*j)-κ*e*k)
  ring

lemma actual_original_difference (κ : ℤ) (x y : Coordinates ℤ) :
    equation κ x-equation κ y =
      equation κ (x-y)+2*originalBilinear κ (x-y) y := by
  simpa only [sub_add_cancel] using actual_original_polarization κ (x-y) y

/-- Exact linearization of the original phase. No nondegeneracy,
primality or coprimality hypothesis is needed for this finite identity. -/
lemma actual_original_phase_difference (κ : ℤ) (x y : Coordinates ℤ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (equation κ x) θ * starRingEnd ℂ (fourier (equation κ y) θ) =
      fourier (equation κ (x-y)) θ *
        fourier (2*originalBilinear κ (x-y) y) θ := by
  rw [←fourier_neg,←fourier_add,←fourier_add]
  congr 1
  simpa only [sub_eq_add_neg] using actual_original_difference κ x y

end ActualOriginalQuadraticPolarization318
