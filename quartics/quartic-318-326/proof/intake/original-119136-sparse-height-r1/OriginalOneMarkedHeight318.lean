module
public import OriginalTwoMarkedTensorsR8_318
public import OriginalRawScalarCalibration318
public section
noncomputable section

namespace OriginalOneMarkedHeight318

open NumberField OriginalGlobalHodgeIdealHeight318 OriginalRawScalarCalibration318
open SelectedSameADirectBicanonicalHeight318
open scoped TensorProduct nonZeroDivisors

variable {E H2 D2 : Type*} [Field E] [NumberField E] [AddCommGroup H2] [Module E H2]
  [AddCommGroup D2] [Module E D2]

/-- Geometric information to be obtained from the actual canonical germ at
one embedding. B is already fixed by the one common, ordinary raw KS. -/
structure Germ (w : InfinitePlace E) (t : ℚ) (B : E) (arch : ℝ) where
  tau : ℂ
  derivT : ℂ
  frame : ℂ
  positive : 0 < tau.im
  deriv_nonzero : derivT ≠ 0
  frame_nonzero : frame ≠ 0
  raw : w.embedding B =
    210 * frame^2 / (((2 * (Real.pi : ℂ)) * Complex.I)^2 * derivT^2)
  metric : arch^2 = 210 * ‖frame‖^2 * tau.im^2 / Real.pi^2
  compact : 64 * (SelectedActualSameACurvature64.metricU (w.embedding (t : E)) *
    ‖derivT‖^2 * tau.im^2) ≤ OriginalMarkedHeightCalibration318.denominator (w.embedding (t : E))

/-- The actual overlap and its inverse-section tensors determine the finite
lattice/reads. The actual complex germs are calibrated against the same
rational raw KS, not an extra freely chosen scalar, Hodge line or marked t.
No +11 hypothesis or normalized height is supplied. -/
theorem lower_height
    (S3 S11 C : Type*) [CommRing S3] [CommRing S11] [CommRing C]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) C]
    [Algebra S3 E] [Algebra S11 E] [Algebra C E] [Algebra S3 C] [Algebra S11 C]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) C E]
    [IsScalarTower S3 C E] [IsScalarTower S11 C E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S3 M] [Module S11 N]
    [Module.Finite S3 M] [Module.Finite S11 N]
    (f : M →ₗ[S3] E) (g : N →ₗ[S11] E) (nz : ∃ m, f m ≠ 0)
    (mark : C ⊗[S3] M ≃ₗ[C] C ⊗[S11] N)
    (wedge : (OriginalHodgeModuleOverlap318.read (C:=C) g).comp mark.toLinearMap =
      OriginalHodgeModuleOverlap318.read f)
    (z3 : Fin 2 → M ⊗[S3] M) (z11 : Fin 2 → N ⊗[S11] N)
    (η : H2 ≃ₗ[E] E) (dt : D2 ≃ₗ[E] E) (ψ : H2 ≃ₗ[E] D2) (y : Fin 2 → D2)
    (at3 : ∀ i, ψ (η.symm (OriginalTwoMarkedTensorsR8_318.square f (z3 i))) = (210:E) • y i)
    (at11 : ∀ i, ψ (η.symm (OriginalTwoMarkedTensorsR8_318.square g (z11 i))) = (210:E) • y i)
    (t : ℚ) (P0 : P (t:E) ≠ 0) (readT : ∀ i, P (t:E) * dt (y i) = coefficients (F:=E) t i)
    (arch : InfinitePlace E → ℝ) (pos : ∀ w, 0 < arch w)
    (germs : ∀ w : InfinitePlace E, Germ w t (dt (ψ (η.symm 1))) (arch w)) :
    ∃ (I : FractionalIdeal (𝓞 E)⁰ E) (hn : I ≠ 0),
      (I:Submodule (𝓞 E) E) = f.range.restrictScalars (𝓞 E) ⊓ g.range.restrictScalars (𝓞 E) ∧
      Height.logHeight₁ (t/32) < 2*(idealFrame I hn arch pos).normalizedDegree + 11 := by
  refine OriginalTwoMarkedTensorsR8_318.height S3 S11 C f g nz mark wedge z3 z11
    η dt ψ y at3 at11 t (P (t:E)) P0 readT arch pos ?_
  intro w
  let R := germs w
  exact finite_period w t (dt (ψ (η.symm 1))) (arch w)
    (from_signed_period w t _ R.tau R.derivT R.frame _ R.positive
      R.deriv_nonzero R.frame_nonzero P0 R.raw R.metric R.compact)

end OriginalOneMarkedHeight318

#print axioms OriginalOneMarkedHeight318.lower_height
