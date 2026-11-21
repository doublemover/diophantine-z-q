module

public import SelectedActualUpperHalfPlanePrimitive318
public import SelectedWeightTwoPetersson318
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

public section

noncomputable section

open Filter Function Set UpperHalfPlane
open scoped Topology Manifold
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open DerivativeCocycle318 SelectedWeightTwoPetersson318
open SelectedActualUpperHalfPlanePrimitive318

namespace SelectedActualOrdinaryAbelPeriodMap318

variable {M g : ℕ}

private theorem ordinary_coeff_holo (f : Form M) :
    DifferentiableOn ℂ (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) upperHalfPlaneSet :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)

/-- The primitive of the actual weight-two coefficient in the same
ordinary frame, normalized at the literal period I. -/
def primitive (f : Form M) : ℂ → ℂ :=
  Classical.choose (exists_normalized_primitive _ (ordinary_coeff_holo f))

private theorem primitive_spec (f : Form M) :
    primitive f Complex.I = 0 ∧
      ∀ z ∈ upperHalfPlaneSet,
        HasDerivAt (primitive f) (f (UpperHalfPlane.ofComplex z)) z := by
  unfold primitive
  exact Classical.choose_spec (exists_normalized_primitive _ (ordinary_coeff_holo f))

theorem primitive_I (f : Form M) : primitive f Complex.I = 0 := (primitive_spec f).1

theorem primitive_hasDerivAt (f : Form M) (τ : UpperHalfPlane) :
    HasDerivAt (primitive f) (f τ) (τ : ℂ) := by
  simpa only [UpperHalfPlane.ofComplex_apply] using (primitive_spec f).2 (τ : ℂ) τ.im_pos

/-- A literal modular period vector in the original frame, one path
from I to the translated I. It is computed using the same primitive,
not by an independent choice of period lattice. -/
def modularPeriod (f : Fin g → Form M) (γ : image M) : Fin g → ℂ :=
  fun i => primitive (f i) (↑(γ • UpperHalfPlane.I) : ℂ)

def primitiveVector (f : Fin g → Form M) (τ : UpperHalfPlane) : Fin g → ℂ :=
  fun i => primitive (f i) (τ : ℂ)

private def mobius (γ : image M) (z : ℂ) : ℂ :=
  ↑((γ : G) • UpperHalfPlane.ofComplex z)

private theorem mobius_value (γ : image M) (τ : UpperHalfPlane) :
    mobius γ (τ : ℂ) = ↑(γ • τ) := by
  unfold mobius
  rw [UpperHalfPlane.ofComplex_apply]
  rfl

private theorem primitive_mobius_derivative (f : Form M) (γ : image M) (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => primitive f (mobius γ z)) (f τ) (τ : ℂ) := by
  have hg : HasDerivAt (mobius γ) (derivative (γ : G) τ) (τ : ℂ) :=
    (UpperHalfPlane.hasStrictDerivAt_smul ((γ : G).property) τ).hasDerivAt
  have ho : HasDerivAt (primitive f) (f (γ • τ)) (mobius γ (τ : ℂ)) := by
    rw [mobius_value γ τ]
    exact primitive_hasDerivAt f (γ • τ)
  have h := ho.comp (τ : ℂ) hg
  rw [differential_pullback f γ τ] at h
  simpa only [Function.comp_def] using h

private theorem primitive_smul (f : Form M) (γ : image M) (τ : UpperHalfPlane) :
    primitive f (↑(γ • τ) : ℂ) =
      primitive f (τ : ℂ) + primitive f (↑(γ • UpperHalfPlane.I) : ℂ) := by
  let C : ℂ := primitive f (↑(γ • UpperHalfPlane.I) : ℂ)
  let F : ℂ → ℂ := fun z => primitive f (mobius γ z)
  let H : ℂ → ℂ := fun z => primitive f z + C
  have hF (z : ℂ) (hz : z ∈ upperHalfPlaneSet) :
      HasDerivAt F (f (UpperHalfPlane.ofComplex z)) z := by
    let t : UpperHalfPlane := ⟨z,hz⟩
    have ht : UpperHalfPlane.ofComplex z = t := UpperHalfPlane.ofComplex_apply_of_im_pos hz
    rw [ht]
    exact primitive_mobius_derivative f γ t
  have hH (z : ℂ) (hz : z ∈ upperHalfPlaneSet) :
      HasDerivAt H (f (UpperHalfPlane.ofComplex z)) z := ((primitive_spec f).2 z hz).add_const C
  have hbase : F Complex.I = H Complex.I := by
    change primitive f (mobius γ (↑UpperHalfPlane.I : ℂ)) = primitive f Complex.I + C
    rw [mobius_value,primitive_I,zero_add]
  have he : upperHalfPlaneSet.EqOn F H := by
    apply isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq
      (𝕜 := ℂ) (f := F) (g := H) (x := Complex.I)
      (convex_halfSpace_im_gt 0).isPreconnected
    · exact fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
    · exact fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
    · intro z hz
      exact (hF z hz).deriv.trans (hH z hz).deriv.symm
    · exact Complex.I_im.symm ▸ (zero_lt_one : (0 : ℝ) < 1)
    · exact hbase
  have h : primitive f (mobius γ (τ : ℂ)) = primitive f (τ : ℂ) + C :=
    he τ.im_pos
  rw [mobius_value] at h
  exact h

theorem vector_smul (f : Fin g → Form M) (γ : image M) (τ : UpperHalfPlane) :
    primitiveVector f (γ • τ) = primitiveVector f τ + modularPeriod f γ := by
  funext i
  exact primitive_smul (f i) γ τ

/-- Actual periods are additive under consecutive deck motions.
This uses the exact derivative cocycle of the fixed ordinary frame. -/
theorem period_mul (f : Fin g → Form M) (γ δ : image M) :
    modularPeriod f (γ * δ) = modularPeriod f γ + modularPeriod f δ := by
  change primitiveVector f ((γ * δ) • UpperHalfPlane.I) = _
  rw [mul_smul, vector_smul]
  exact add_comm _ _

variable {J : Type*} [AddCommGroup J]

/-- The actual ordinary Abel period formula into the supplied exponential
of the same algebraic J_X. The period vanishing hypothesis is the
specific integral-period comparison for that exponential, not a new
choice of target group or lattice inside this construction. -/
def ordinaryAbel (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J)
    (hPeriod : ∀ γ : image M, q (modularPeriod f γ) = 0) : Base (image M) → J :=
  Quotient.lift (fun τ : UpperHalfPlane => q (primitiveVector f τ)) (by
    intro a b hab
    obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp hab
    rw [← hγ, vector_smul, map_add, hPeriod γ, add_zero])

theorem ordinaryAbel_value (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J)
    (hPeriod : ∀ γ : image M, q (modularPeriod f γ) = 0) (τ : UpperHalfPlane) :
    ordinaryAbel f q hPeriod (quotientMap M τ) = q (primitiveVector f τ) := by
  unfold ordinaryAbel
  rfl

theorem ordinaryAbel_continuous [TopologicalSpace J]
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J)
    (hPeriod : ∀ γ : image M, q (modularPeriod f γ) = 0) (hq : Continuous q) :
    Continuous (ordinaryAbel f q hPeriod) := by
  have hπ : IsQuotientMap (quotientMap M) :=
    MulAction.isOpenQuotientMap_quotientMk.isQuotientMap
  apply hπ.continuous_iff.mpr
  have hc : Continuous (primitiveVector f) := by
    apply continuous_pi
    intro i
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact (primitive_hasDerivAt (f i) τ).continuousAt.comp continuous_coe.continuousAt
  have he : ordinaryAbel f q hPeriod ∘ quotientMap M = q ∘ primitiveVector f :=
    funext (ordinaryAbel_value f q hPeriod)
  rw [he]
  exact hq.comp hc

end SelectedActualOrdinaryAbelPeriodMap318

#print axioms SelectedActualOrdinaryAbelPeriodMap318.period_mul
#print axioms SelectedActualOrdinaryAbelPeriodMap318.ordinaryAbel_value
#print axioms SelectedActualOrdinaryAbelPeriodMap318.ordinaryAbel_continuous
