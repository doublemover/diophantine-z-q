module
public import QuarticJacobiIntegral318
public import CanonicalCurveParity318
public section
noncomputable section
namespace CanonicalJacobiNorm318
open CanonicalJacobiTrace318 QuarticJacobiIntegral318 FiniteCurveCharacterCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma jacobi_star (ψ φ : MulChar F ℂ) :
    star (jacobiSum ψ φ)=jacobiSum ψ⁻¹ φ⁻¹ := by
  change (starRingEnd ℂ) (∑ t : F, ψ t*φ (1-t))=jacobiSum ψ⁻¹ φ⁻¹
  rw [map_sum,jacobiSum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [map_mul]
  change star (ψ t)*star (φ (1-t))=ψ⁻¹ t*φ⁻¹ (1-t)
  rw [MulChar.star_apply',MulChar.star_apply']

lemma quadratic_nontrivial (hF : ringChar F≠2) : (quadraticComplex:MulChar F ℂ)≠1 := by
  obtain ⟨a,ha⟩ := quadraticChar_exists_neg_one' hF
  intro he
  have h := congrArg (fun χ : MulChar F ℂ => χ (a:F)) he
  rw [quadraticComplex_apply,ha,MulChar.one_apply a.isUnit] at h
  norm_num at h

/-- The constructed quartic Jacobi sum has norm #F by the pinned Gauss/Jacobi
identity; the original quadratic character and all nontriviality inputs are checked. -/
theorem actual_norm (hF : ringChar F≠2) (hchar : ringChar ℂ≠ringChar F)
    (ψ : MulChar F ℂ) (hsq : ψ^2=quadraticComplex) (hfour : ψ^4=1) :
    jacobiSum ψ quadraticComplex*star (jacobiSum ψ quadraticComplex)=(Fintype.card F:ℂ) := by
  have hχ := quadratic_nontrivial hF
  have hψ : ψ≠1 := by intro he; rw [he,one_pow] at hsq; exact hχ hsq.symm
  have hprod : ψ*quadraticComplex≠1 := by
    intro he
    have hthree : ψ^3=1 := by calc
      _ = ψ*(ψ^2) := by group
      _ = 1 := by rw [hsq,he]
    have hone : ψ=1 := by calc
      ψ = ψ^4*(ψ^3)⁻¹ := by group
      _ = 1 := by rw [hfour,hthree]; simp
    exact hψ hone
  have hn := jacobiSum_mul_jacobiSum_inv hchar hψ hχ hprod
  rwa [←jacobi_star] at hn

/-- Produce the integer Gaussian coordinates of the actual quartic Jacobi
sum, its norm and its comparison with the actual canonical character trace. -/
theorem integral_trace_norm (hF : ringChar F≠2) (hchar : ringChar ℂ≠ringChar F)
    (hminus : quadraticChar F (-1:F)=1) (h4 : 4∣Fintype.card F-1) :
    ∃ c d : ℤ, c^2+d^2=(Fintype.card F:ℤ) ∧ traceSum (1:F)=2*c := by
  obtain ⟨ψ,hsq,hfour⟩ := CanonicalQuarticCharacter318.exists_quartic hF h4
  obtain ⟨c,d,hJ⟩ := jacobi_integral ψ hfour
  have hn := actual_norm hF hchar ψ hsq hfour
  have hs := trace_jacobi hF hminus ψ hsq hfour
  have hχinv : (quadraticComplex:MulChar F ℂ)⁻¹=quadraticComplex :=
    ((quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)).inv
  have hstar := jacobi_star ψ quadraticComplex
  rw [hχinv] at hstar
  rw [←hstar] at hs
  have hnr := congrArg Complex.re hn
  have hsr := congrArg Complex.re hs
  simp [hJ,Complex.mul_re,Complex.mul_im] at hnr hsr
  have hnormR : (c:ℝ)^2+(d:ℝ)^2=(Fintype.card F:ℝ) := by nlinarith
  have htraceR : (traceSum (1:F):ℝ)=2*(c:ℝ) := by linarith
  exact ⟨c,d,by exact_mod_cast hnormR,by exact_mod_cast htraceR⟩

/-- The canonical CM input is now produced from the actual finite-field
Jacobi sum, with parity supplied by the actual four torsion classes. -/
theorem canonical_from_ray (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b) : CanonicalSelectedCounts318.CanonicalCM p a := by
  have hmod := GaussianRayQuadratic318.prime_mod p a b hray
  have hp4 : p%4=1 := by omega
  have hp2 : p≠2 := by omega
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hchar : ringChar ℂ≠ringChar (ZMod p) := by
    have hz : ringChar ℂ=0 := by simp
    rw [hz,ringChar_zmod_n]
    exact Ne.symm (Nat.ne_of_gt (Fact.out : p.Prime).pos)
  have hminus : quadraticChar (ZMod p) (-1:ZMod p)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
  have h4 : 4∣Fintype.card (ZMod p)-1 := by rw [ZMod.card]; omega
  obtain ⟨c,d,hn,ht⟩ := integral_trace_norm hF hchar hminus h4
  have hcod := CanonicalCurveParity318.odd_half_trace p hp4 c ht
  apply CanonicalCMNormBridge318.canonical_of_norm p a b c d hray
    (by simpa only [ZMod.card] using hn) hcod ht

end CanonicalJacobiNorm318
