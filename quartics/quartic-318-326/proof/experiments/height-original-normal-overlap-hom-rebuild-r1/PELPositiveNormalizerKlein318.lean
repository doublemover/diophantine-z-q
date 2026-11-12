module
public import PELOriginalKleinEquivariance318
public import PELPositiveNormalizerMobius318
public section
noncomputable section
namespace PELPositiveNormalizerKlein318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalKleinEquivariance318 PELQuaternionKleinAction318 PELDirichletHeight318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
set_option maxHeartbeats 2400000

/-- Each original rational homogeneous row evaluated at arbitrary REAL
scaled coordinates. No rational-point restriction or determinant-one
normalization is imposed. -/
@[expose] def realRow (q : B) (i : Fin 3) (A Y : ℝ) : ℝ :=
  ((PELQuaternionKleinAction318.matrix q i 0:ℚ):ℝ)*A+
  ((PELQuaternionKleinAction318.matrix q i 1:ℚ):ℝ)*Y+
  ((PELQuaternionKleinAction318.matrix q i 2:ℚ):ℝ)

theorem original_row (g : positiveNormalizer) (τ : HalfPlane) (i : Fin 3) :
    realRow (g.val:B) i (scaledFirst τ) (scaledSecond τ)=
      originalVector (PELPositiveNormalizerMobius318.matrix g) τ i := by
  rw [originalVector,←PELQuaternionKleinAction318.original_real_matrix]
  simp [realRow,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem original_denominator_positive (g : positiveNormalizer) (τ : HalfPlane) :
    0<realRow (g.val:B) 2 (scaledFirst τ) (scaledSecond τ) := by
  rw [original_row,(vector_values (PELPositiveNormalizerMobius318.matrix g) τ).2.2]
  apply div_pos
  · have hl : 0<lowerNorm (PELPositiveNormalizerMobius318.matrix g) τ :=
      Complex.normSq_pos.mpr (QuaternionicPositiveDeterminant318.denominator_nonzero
        _ (matrix_positive g) τ τ.property)
    have hu : 0≤upperNorm (PELPositiveNormalizerMobius318.matrix g) τ := Complex.normSq_nonneg _
    linarith
  · nlinarith [Complex.normSq_nonneg (τ:ℂ)]

/-- Actual positive-determinant equivariance in original scaled Klein
coordinates. The earlier determinant-one theorem is not applied to a
normalizer with a different reduced norm. -/
theorem original_scaled_action (g : positiveNormalizer) (τ : HalfPlane) :
    scaledFirst (baseAction g τ)=
      realRow (g.val:B) 0 (scaledFirst τ) (scaledSecond τ)/
        realRow (g.val:B) 2 (scaledFirst τ) (scaledSecond τ) ∧
    scaledSecond (baseAction g τ)=
      realRow (g.val:B) 1 (scaledFirst τ) (scaledSecond τ)/
        realRow (g.val:B) 2 (scaledFirst τ) (scaledSecond τ) := by
  let M := PELPositiveNormalizerMobius318.matrix g
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hd : 0<lowerNorm M τ :=
    Complex.normSq_pos.mpr (QuaternionicPositiveDeterminant318.denominator_nonzero
      M (matrix_positive g) τ τ.property)
  have hs : upperNorm M τ+lowerNorm M τ≠0 := by
    have hu : 0≤upperNorm M τ := Complex.normSq_nonneg _
    linarith
  have hnorm : Complex.normSq (mobius M τ)=upperNorm M τ/lowerNorm M τ :=
    Complex.normSq_div _ _
  have hre : (mobius M τ).re=crossTerm M τ/lowerNorm M τ := by
    simp only [mobius,Complex.div_re,QuaternionicMobiusPeriods318.denominator,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,add_zero,zero_add,sub_zero,
      crossTerm,lowerNorm]
    ring
  simp only [original_row]
  constructor
  · change alpha*beta*(2*(mobius M τ).re/(Complex.normSq (mobius M τ)+1))=_
    rw [hre,hnorm,(vector_values M τ).1,(vector_values M τ).2.2]
    field_simp [hn,hd.ne',hs] <;> ring
  · change beta*((Complex.normSq (mobius M τ)-1)/(Complex.normSq (mobius M τ)+1))=_
    rw [hnorm,(vector_values M τ).2.1,(vector_values M τ).2.2]
    field_simp [hn,hd.ne',hs] <;> ring

theorem realRow_smul (q : ℚ) (x : B) (i : Fin 3) (A Y : ℝ) :
    realRow (q • x) i A Y=(q:ℝ)^2*realRow x i A Y := by
  fin_cases i <;> simp [realRow,PELQuaternionKleinAction318.matrix] <;> push_cast <;> ring

theorem primitive_denominator_nonzero (g : positiveNormalizer) (q : ℚ) (x : Coordinates)
    (hg : (g.val:B)=q • embed x) (τ : HalfPlane) :
    realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ)≠0 := by
  intro h
  have hp := original_denominator_positive g τ
  rw [hg,realRow_smul,h,mul_zero] at hp
  exact (lt_irrefl 0) hp

/-- The exact primitive rational scalar cancels from every projective row.
This supplies the actual action needed to consume whole-integer equality
certificates, without asserting that an arbitrary norm vector normalizes. -/
theorem primitive_scaled_action (g : positiveNormalizer) (q : ℚ) (hq : q≠0)
    (x : Coordinates) (hg : (g.val:B)=q • embed x) (τ : HalfPlane) :
    scaledFirst (baseAction g τ)=
      realRow (embed x) 0 (scaledFirst τ) (scaledSecond τ)/
        realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ) ∧
    scaledSecond (baseAction g τ)=
      realRow (embed x) 1 (scaledFirst τ) (scaledSecond τ)/
        realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ) := by
  have h := original_scaled_action g τ
  rw [hg] at h
  simp only [realRow_smul] at h
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq
  have hd := primitive_denominator_nonzero g q x hg τ
  constructor
  · rw [h.1]
    field_simp [hqR,hd] <;> ring
  · rw [h.2]
    field_simp [hqR,hd] <;> ring

/-- Concrete row-identity consumer returning actual original point
coordinates. Any later sign/reflection classifier must provide these
identities for the SAME primitive quaternion and point. -/
theorem original_coordinates_of_rows (g : positiveNormalizer) (q : ℚ) (hq : q≠0)
    (x : Coordinates) (hg : (g.val:B)=q • embed x) (τ : HalfPlane) (A Y : ℝ)
    (hA : realRow (embed x) 0 (scaledFirst τ) (scaledSecond τ)=
      A*realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ))
    (hY : realRow (embed x) 1 (scaledFirst τ) (scaledSecond τ)=
      Y*realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ)) :
    (scaledFirst (baseAction g τ),scaledSecond (baseAction g τ))=(A,Y) := by
  have h := primitive_scaled_action g q hq x hg τ
  have hd := primitive_denominator_nonzero g q x hg τ
  apply Prod.ext
  · rw [h.1,hA,mul_div_cancel_right₀ _ hd]
  · rw [h.2,hY,mul_div_cancel_right₀ _ hd]
end PELPositiveNormalizerKlein318
