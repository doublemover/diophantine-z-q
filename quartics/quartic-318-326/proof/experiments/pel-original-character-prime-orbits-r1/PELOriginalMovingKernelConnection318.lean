module
public import PELOriginalPeriodKernelConnection318
public section
noncomputable section
namespace PELOriginalMovingKernelConnection318
open Filter
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalSiegelMatrix318
open PELOriginalPeriodMatrixDerivative318 PELOriginalFlatPeriodKernel318
open PELOriginalPeriodKernelConnection318

/-- Product rule for the ACTUAL period matrix applied to ANY moving
complex vector, not merely the two constant frame vectors. -/
lemma hasDerivAt_moving_period (τ : ℂ) (hτ : τ≠0)
    (v : ℂ → ComplexVectors) (v' : ComplexVectors) (hv : HasDerivAt v v' τ) :
    HasDerivAt (fun z => (omega z).mulVec (v z))
      ((derivative τ).mulVec (v τ)+(omega τ).mulVec v') τ := by
  have hΩ := hasDerivAt_omega τ hτ
  apply hasDerivAt_pi.mpr
  intro i
  have h0 := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hΩ i) 0).mul (hasDerivAt_pi.mp hv 0)
  have h1 := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hΩ i) 1).mul (hasDerivAt_pi.mp hv 1)
  simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_two,add_assoc,add_left_comm,add_comm] using h0.add h1

lemma hasDerivAt_moving_kernel (τ : ℂ) (hτ : τ≠0)
    (v : ℂ → ComplexVectors) (v' : ComplexVectors) (hv : HasDerivAt v v' τ) :
    HasDerivAt (fun z => kernelLift z (v z))
      (-((derivative τ).mulVec (v τ)+(omega τ).mulVec v'),v') τ :=
  (hasDerivAt_moving_period τ hτ v v' hv).neg.prodMk hv

/-- The normal derivative of ANY differentiable kernel section depends
only on its value, not the derivative of its chosen frame coefficients.
This is the actual second-fundamental descent property. -/
theorem moving_normal (τ : ℂ) (hτ : τ≠0)
    (v : ℂ → ComplexVectors) (v' : ComplexVectors) (hv : HasDerivAt v v' τ) :
    periodMap τ (deriv (fun z => kernelLift z (v z)) τ)=
      normalDerivative τ (v τ) := by
  rw [(hasDerivAt_moving_kernel τ hτ v v' hv).deriv,normalDerivative_formula τ hτ]
  change -((derivative τ).mulVec (v τ)+(omega τ).mulVec v')+
    (omega τ).mulVec v'= -(derivative τ).mulVec (v τ)
  abel

/-- The polarization pairing with ANY moving kernel section gives the
same tensor as the constant-frame computation, including all coefficient
variations. No abstract connection coefficient is supplied. -/
theorem moving_pairing (τ : ℂ) (hτ : τ≠0) (z : ComplexVectors)
    (v : ℂ → ComplexVectors) (v' : ComplexVectors) (hv : HasDerivAt v v' τ) :
    symplectic (kernelLift τ z) (deriv (fun w => kernelLift w (v w)) τ)=
      secondPairing τ z (v τ) := by
  rw [(hasDerivAt_moving_kernel τ hτ v v' hv).deriv,secondPairing_formula τ hτ]
  have hi := kernel_isotropic τ z v'
  simp [symplectic,kernelLift,dotProduct,Fin.sum_univ_two] at hi ⊢
  linear_combination hi

/-- Every genuine differentiable section of the full kernel near tau is
handled, not only sections already supplied in the chosen frame. -/
theorem arbitrary_kernel_section (τ : ℂ) (hτ : τ≠0)
    (s : ℂ → Ambient) (s' : Ambient) (hs : HasDerivAt s s' τ)
    (hk : ∀ᶠ z in 𝓝 τ, periodMap z (s z)=0) :
    periodMap τ (deriv s τ)=normalDerivative τ (s τ).2 := by
  have he : s =ᶠ[𝓝 τ] (fun z => kernelLift z (s z).2) := by
    filter_upwards [hk] with z hz
    apply Prod.ext
    · change (s z).1= -(omega z).mulVec (s z).2
      exact eq_neg_of_add_eq_zero_left hz
    · rfl
  have hv : HasDerivAt (fun z => (s z).2) s'.2 τ :=
    (ContinuousLinearMap.snd ℂ ComplexVectors ComplexVectors).hasFDerivAt.comp_hasDerivAt τ hs
  rw [he.deriv_eq]
  exact moving_normal τ hτ (fun z => (s z).2) s'.2 hv
end PELOriginalMovingKernelConnection318
