# Actual ordinary cutoff: native source-only signed Fourier and Fubini leaves

Original 318/326, no Lean run/push. This stages the genuine input
function χ (the same real function in both original divisor slots)
and derives its angular Mellin inversion and normalized kernel
integral, rather than putting the integral as an assumption.

ActualTZLiteralSchwartz318 accepts a real infinitely smooth χ that
vanishes when |u|>1. Its literal exponential tilt g(u)=e^u χ(u)
gets a compact Schwartz map by the pinned Basic constructor (private
pointwise proof as in the previously accepted Fourier r9 Support).
The conventional raw spectrum is Mathlib inverse Fourier on g.
Thus its sign is POSITIVE 2πit u. The paper angular spectrum has
ξ=2πt and φ(ξ)=(2π)^(-1) raw(ξ/(2π)). The native scalar Bochner
substitution is precisely Measure.integral_comp_mul_left at (2π)^(-1);
the same positive scale cancels the Haar factor. The inverse identity
is forward Fourier of this raw spectrum, so the χ row is
∫φ(ξ) exp(-(1+iξ)u)dξ, with no conjugation. The complex-power identity
for each positive d is explicit (real log, denominators L>0).

For the derivative, use the actual raw first moment guaranteed by
Schwartz integrable_pow_mul; Real.deriv_fourier yields multiplier
−2πit. Subtract the transform derivative from its value and multiply
by e^-u concretely. Tilt Leibniz with HasDerivAt.ofReal_comp yields
−χ'(u), precisely the transform of (1+iξ)φ(ξ). There is no assumed
parameter-derivative theorem, and no swapped derivative at an
unproved dominated integral. Transform is itself angularly scaled
Schwartz; every absolute polynomial moment and the threshold tail
H^-j times its j-th moment are formal source declarations.

ActualTZMellinFubini318 obtains norm of a product of two derivative
rows as e^-2u * ‖ψ(ξ)‖*‖ψ(η)‖ with ψ(ξ)=(1+iξ)φ(ξ).
The row continuity and this product majorant prove integrability
for the fixed-ξ (η,u) and joint ((ξ,u),η) product measures,
with u restricted to Ioi 0. This permits the two pinned Fubini
returns (first η/u conditional on fixed ξ; then ξ/u using the
integrable η integral from the triple). Also proves absolute
integrability of the two-frequency kernel directly via the
nonzero denominator. Factoring two equal integrals, not using
conjugation, gives the square of the literal real derivative. The
cutoff guarantees derivative zero on (1,∞); the real slab energy
∫_0^1 |χ'|² then gives the actual complex kernel integral. The
kernel_one_for input is exactly the smooth/support/real-energy
fields of ActualTZJointPolynomialForms318.PublishedCutoff (evenness
and χ(0)>0 unused here); it does NOT assume the complex or angular
integral. The source proper geometry does not need to construct an
alternative cutoff or touch any prime support.

Exact donor: old ActualTZMellinKernel318 SHA 4370176f… (mode,
norm bound, nonzero sum and signed positive half-line Laplace). No
ζ ratio, Euler edge or ordinary full (68) dependency is required
for these two leaves. Neither verified native moment nor
Mellin–Euler infinite interchange nor nonlinear PET is claimed.

Pinned primary Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679:
- FourierTransformDeriv.lean local git blob 83fbc390… lines 764–788
  (Real.hasDerivAt_fourier, Real.deriv_fourier).
- Distribution/SchwartzSpace/Fourier.lean 92, 111, 120–131
  (function coercions and forward/inverse pair).
- Distribution/SchwartzSpace/Basic.lean 496–510, 921–925 and
  1030–1038 (compact producer, linear composition, L¹ moments).
- MeasureTheory/Integral/Prod.lean 272–274, 303–307, 435–438
  (product integrability, marginal integrability, actual swaps).
- MeasureTheory/Integral/Bochner/Set.lean 416–419, 663–681
  (zero outside slab and measurable threshold tail comparison).
