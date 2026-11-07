module
public import ActualJInvariant318
public import HolomorphicInverse318
public import ModularWeierstrass318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open HolomorphicCharts318
open scoped Manifold ContDiff MatrixGroups
namespace QuotientJ318
set_option maxHeartbeats 0

/-- The actual modular invariant is holomorphic on the upper half-plane. -/
theorem j_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ActualQJ318.jInvariant := by
  have he : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (ModularForm.E (k:=4) (by norm_num) : UpperHalfPlane → ℂ) :=
    (ModularForm.E (k:=4) (by norm_num)).holo'
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ModularForm.discriminant := by
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (CuspForm.discriminant : UpperHalfPlane → ℂ)
    exact CuspForm.discriminant.holo'
  have hj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ActualQJ318.jInvariant :=
    (he.pow 3).div hd ModularForm.discriminant_ne_zero
  intro tau
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  exact ((UpperHalfPlane.mdifferentiable_iff.mp hj).analyticOnNhd
    isOpen_upperHalfPlaneSet tau tau.im_pos).contDiffAt

/-- Invariance under the actual fine-level matrix image. -/
theorem image_invariant (N:ℕ) (g:image N) (tau:UpperHalfPlane) :
    ActualQJ318.jInvariant (g • tau)=ActualQJ318.jInvariant tau := by
  apply ActualJInvariant318.modular_invariant
  obtain ⟨gamma,hgamma⟩ := g.property
  rw [←hgamma]
  exact ⟨gamma.val,rfl⟩

/-- The actual analytic j-invariant descends to the genuine orbit quotient. -/
@[expose] def jMap (N:ℕ) : Base (image N) → ℂ :=
  Quotient.lift ActualQJ318.jInvariant (by
    intro a b hab
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hab
    rw [←hg]
    exact image_invariant N g b)

@[simp] theorem jMap_projection (N:ℕ) (tau:UpperHalfPlane) :
    jMap N (quotientMap N tau)=ActualQJ318.jInvariant tau := rfl

/-- Its value at every lift is the genuine algebraic j of the actual
normalized Weierstrass model, not a supplied model-identification premise. -/
theorem jMap_curve_j (N:ℕ) (tau:UpperHalfPlane) :
    jMap N (quotientMap N tau)=(ModularWeierstrass318.curve tau).j :=
  (ModularWeierstrass318.curve_j tau).symm

end QuotientJ318
