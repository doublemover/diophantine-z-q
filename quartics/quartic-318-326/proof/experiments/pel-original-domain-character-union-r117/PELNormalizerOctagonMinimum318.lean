module
public import PELNormalizerOctagonAffine318
public import PELOriginalKleinEquivariance318
public import PELNormalizerPrimitiveRepresentative318
public import PELPositiveNormalizerMobius318
public section
noncomputable section
namespace PELNormalizerOctagonMinimum318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELQuaternionKleinAction318 PELNormalizerOctagonVertices318 PELNormalizerOctagonAffine318
open NormalizerVertexEnergyMinimum318 PELLevelThreeSimilitudes318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELOriginalKleinEquivariance318 PELDirichletHeight318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
set_option maxHeartbeats 2400000

@[expose] def realDen (q : B) (A Y : ℝ) : ℝ :=
  ((PELQuaternionKleinAction318.matrix q 2 0:ℚ):ℝ)*A+((PELQuaternionKleinAction318.matrix q 2 1:ℚ):ℝ)*Y+((PELQuaternionKleinAction318.matrix q 2 2:ℚ):ℝ)

theorem realDen_cast (q : B) (P : Point) : realDen q P.1 P.2=(PELQuaternionKleinAction318.denominator q P:ℝ) := by
  simp [realDen,PELQuaternionKleinAction318.denominator,vector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem integer_whole_octagon (i : Fin 16) (x : Coordinates)
    (hx : integerNorm x=(allowedNorm i:ℤ)) (A Y : ℝ) (hP : inequalities A Y) :
    (allowedNorm i:ℝ)≤realDen (embed x) A Y := by
  apply whole_octagon (allowedNorm i:ℝ) _ _ _ A Y hP
  intro v
  have hq := all_vertex_minimum i x hx v
  have h := realDen_cast (embed x) (vertex v)
  change (allowedNorm i:ℝ)≤realDen (embed x) (vertex v).1 (vertex v).2
  rw [h]
  exact_mod_cast hq

theorem realDen_smul (q : ℚ) (x : B) (A Y : ℝ) :
    realDen (q • x) A Y=(q:ℝ)^2*realDen x A Y := by
  simp [realDen,PELQuaternionKleinAction318.matrix]
  push_cast
  ring

/-- The complete actual positive normalizer, not merely the16 words,
satisfies the inequality at every REAL point of the literal octagon. -/
theorem full_normalizer_denominator (g : positiveNormalizer) (A Y : ℝ)
    (hP : inequalities A Y) : (reducedNorm (g.val:B):ℝ)≤realDen (g.val:B) A Y := by
  let G : PELActualOrderNormalizer318.normalizer := ⟨g.val,g.property.1⟩
  obtain ⟨q,x,z,w,hg,hx,hprim,hdiv,hnorm⟩ :=
    PELNormalizerPrimitiveRepresentative318.primitive_representative G
  have hq : 0<(q:ℚ)^2 := sq_pos_of_ne_zero q.ne_zero
  have hNQ : 0<(integralNorm x:ℚ) := by
    have hh : 0<(q:ℚ)^2*(integralNorm x:ℚ) := by rw [←hnorm]; exact g.property.2
    exact pos_of_mul_pos_left hh hq.le
  have hN : 0<integralNorm x := by exact_mod_cast hNQ
  let N := (integralNorm x).toNat
  have hNZ : (N:ℤ)=integralNorm x := Int.toNat_of_nonneg hN.le
  have hNp : 0<N := by exact_mod_cast (show (0:ℤ)<(N:ℤ) by rwa [hNZ])
  have hNd : N∣210 := by exact_mod_cast (show (N:ℤ)∣210 by rwa [hNZ])
  obtain ⟨i,hi⟩ := positive_divisor_cases N hNp hNd
  have hxi : integerNorm x=(allowedNorm i:ℤ) := by
    change integralNorm x=(allowedNorm i:ℤ)
    rw [←hNZ,hi]
  have hd := integer_whole_octagon i x hxi A Y hP
  have hval : (g.val:B)=(q:ℚ) • embed x := by
    change (G.val:B)=_
    rw [hg]
    change algebraMap ℚ B (q:ℚ)*(w.val:B)=_
    rw [←hx,Algebra.smul_def]
  have hnormR : (reducedNorm (g.val:B):ℝ)=(q:ℝ)^2*(allowedNorm i:ℝ) := by
    have hh := hnorm
    change reducedNorm (g.val:B)=(q:ℚ)^2*(integralNorm x:ℚ) at hh
    have hnx : integralNorm x=(allowedNorm i:ℤ) := hxi
    rw [hnx] at hh
    exact_mod_cast hh
  rw [hnormR,hval,realDen_smul]
  exact mul_le_mul_of_nonneg_left hd (sq_nonneg (q:ℝ))

/-- The original positive-determinant height identity retains its actual
reduced norm, unlike the norm-one special case. -/
theorem positive_height_multiplier (g : positiveNormalizer) (τ : HalfPlane) :
    height (baseAction g τ)=
      realDen (g.val:B) (scaledFirst τ) (scaledSecond τ)/
        (reducedNorm (g.val:B):ℝ)*height τ := by
  let M := PELPositiveNormalizerMobius318.matrix g
  have hd : 0<Complex.normSq (QuaternionicMobiusPeriods318.denominator M τ) :=
    Complex.normSq_pos.mpr (QuaternionicPositiveDeterminant318.denominator_nonzero
      M (matrix_positive g) τ τ.property)
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hgN : (reducedNorm (g.val:B):ℝ)≠0 := by exact_mod_cast g.property.2.ne'
  have hdet : M.det=(reducedNorm (g.val:B):ℝ) :=
    PELPeriodDeterminant318.representation_det (g.val:B)
  have hv : realDen (g.val:B) (scaledFirst τ) (scaledSecond τ)=originalVector M τ 2 := by
    rw [originalVector,←PELQuaternionKleinAction318.original_real_matrix]
    simp [realDen,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  rw [hv,(vector_values M τ).2.2]
  change (Complex.normSq (mobius M τ)+1)/(mobius M τ).im=_
  rw [QuaternionicPositiveDeterminant318.mobius_im_det,hdet]
  simp only [mobius,Complex.normSq_div]
  unfold upperNorm lowerNorm height
  field_simp [hd.ne',hgN,hn,τ.property.ne'] <;> ring

/-- Every actual original positive normalizer increases height on the
literal octagon. The group is not replaced by a finite table of words. -/
theorem original_all_normalizer_minimum (τ : HalfPlane)
    (hτ : inequalities (scaledFirst τ) (scaledSecond τ)) (g : positiveNormalizer) :
    height τ≤height (baseAction g τ) := by
  have hd := full_normalizer_denominator g (scaledFirst τ) (scaledSecond τ) hτ
  have hn : 0<(reducedNorm (g.val:B):ℝ) := by exact_mod_cast g.property.2
  rw [positive_height_multiplier]
  have hratio : 1≤realDen (g.val:B) (scaledFirst τ) (scaledSecond τ)/
      (reducedNorm (g.val:B):ℝ) := (le_div_iff₀ hn).mpr (by simpa using hd)
  nlinarith [height_pos τ]
end PELNormalizerOctagonMinimum318
