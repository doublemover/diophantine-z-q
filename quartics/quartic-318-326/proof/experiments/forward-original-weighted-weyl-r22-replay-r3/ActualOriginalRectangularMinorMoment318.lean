module
public import ActualOriginalFiveQuadraticMoment318
public section
noncomputable section
namespace ActualOriginalRectangularMinorMoment318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318 ActualOriginalFiniteCircleIdentity318
open ActualOriginalQuadraticFourthMoment318 ActualOriginalFiniteFourierEnergy318
open ActualOriginalQuadraticEnergyCount318 ActualOriginalFiveQuadraticMoment318
open ActualOriginalMajorArcDomain318 MeasureTheory
open scoped BigOperators

/-- Exact factorization only for the ORIGINAL UNWEIGHTED rectangle.
It does not factor an arbitrary original smooth weight. -/
lemma actual_original_rectangle_factorization (κ : ℤ) (s0 s1 s2 s3 s4 : Finset ℤ)
    (θ : AddCircle (1 : ℝ)) :
    originalCircleSum κ (originalBox s0 s1 s2 s3 s4) (fun _ => 1) θ=
      quadraticSum s0 1 θ*quadraticSum s1 1 θ*quadraticSum s2 (-1) θ*
      quadraticSum s3 (-1) θ*quadraticSum s4 (-κ) θ := by
  have hp (x : Coordinates ℤ) : fourier (equation κ x) θ=
      fourier (x.1.1^2) θ*fourier (x.1.2^2) θ*fourier (-x.2.1.1^2) θ*
      fourier (-x.2.1.2^2) θ*fourier ((-κ)*x.2.2^2) θ := by
    simp only [←fourier_add]
    congr 1
    dsimp [equation]
    ring
  simp only [originalCircleSum,Finset.sum_apply,one_mul,hp,originalBox,Finset.sum_product,
    quadraticSum,frequencySum,Finset.sum_mul,Finset.mul_sum,neg_one_mul]

/-- The four genuine quadratic moments now control the actual original
five-variable rectangular minor integral from ONE fifth-factor supremum.
This is the precise consumer needed by a later integrated weighted Abel
argument, not a claim that the weighted full sum already factors. -/
theorem actual_original_rectangle_minor_moment (κ : ℤ) (N H : ℕ) (B : ℝ)
    (s0 s1 s2 s3 s4 : Finset ℤ)
    (hs0 : s0⊆Finset.Icc (-(H : ℤ)) H) (hs1 : s1⊆Finset.Icc (-(H : ℤ)) H)
    (hs2 : s2⊆Finset.Icc (-(H : ℤ)) H) (hs3 : s3⊆Finset.Icc (-(H : ℤ)) H)
    (δ : ℝ) (hδ : 0<δ) (M : ℝ) (hM : 0≤M)
    (h4 : ∀ t∈minorDomain N B, ‖quadraticSum s4 (-κ) (t : AddCircle (1 : ℝ))‖≤M) :
    (∫ t in minorDomain N B,
      ‖originalCircleSum κ (originalBox s0 s1 s2 s3 s4) (fun _ => 1) (t : AddCircle (1 : ℝ))‖)≤
      M*momentBudget H δ := by
  simp_rw [actual_original_rectangle_factorization]
  apply actual_five_quadratic_moment H s0 s1 s2 s3 s4 hs0 hs1 hs2 hs3
    1 1 (-1) (-1) (-κ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    δ hδ (-radius N B) (minorDomain N B) (minor_measurable N B) _ M hM h4
  intro t ht
  change -radius N B<t ∧ t≤ -radius N B+1
  have hh := ht.1
  change -radius N B<t ∧ t≤1-radius N B at hh
  constructor <;> linarith [hh.1,hh.2]

end ActualOriginalRectangularMinorMoment318
