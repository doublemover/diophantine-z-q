# Exact even central value in the same E323 Heegner datum

The same h_* = −455, E=E323, K=Q(√−455) and elliptic curve
E^h*=E_{−146965} as in the authentic finite detector. Write
D=146965, a positive fundamental discriminant coprime to 48.
The earlier exact arithmetic interval (not a floating estimate)
encloses the sign-+ central value in
[9.005662277298974, 9.005687002386926].
This note pins the primitive real/imaginary period normalization
and gives \(L_*(h_*)=2048\), exactly.

## Integral modular period; no analytic converse used

Let \(\phi_0:X_0(48)\to E_{-1}\) be the rational quotient used
for the actual finite calculations. Its nonconstant
differential lies in the genuine level-48 elliptic newform
line (or the same chosen rational optimal quotient arrow).
On the normalized cusp ∞ chart from the thesis, x~q⁻¹,
y~q⁻⁴, \(z=(x-1/x)/2\sim1/(2q)\), and the quartic branch
\(v^2=z^4+z^2+1\) has \(v=z²+1/2+O(z^{-2})\).
The raw elliptic map \(X=2(v+1)/z²+1\),
\(Y=2(((v+1)/z²)^2-1)z\) consequently has
\(X=3+12q²+O(q³), Y=12q+O(q²)\).
Thus \(\phi_0^*(dX/(2Y))=(1+O(q))\,dq\).
Translation by the exact cusp (3,0) does not change it.
This fixes the newform multiple to +1 with first coefficient
one: \(\phi_0^*\omega=f(q)dq/q\). The displayed differential is
minimal on the actual models, since all integral discriminant
valuations of \(E_{-1}\) and \(E_{323}\) are strictly below 12.

For every a coprime to D, the cuspidal rational value a/D
represents the cusp 0 of X0(48), by choosing a matrix with second
column (a,D), bottom-left divisible by 48, and determinant 1.
This is possible by Bezout because gcd(D,48a)=1. The genuine
paths \(I_a=[\infty,a/D]\) thus have the same boundary. The integer
weighted sum \(C=\sum_{a\bmod D}\chi_D(a) I_a\) is a closed integral
cycle: the nontrivial primitive character sums to zero.
By Fourier integral and the **unaveraged** Gauss identity
\(\sum_a \chi_D(a)e^{2\pi ian/D}=\tau_D \chi_D(n)\),
\(\int_C\phi_0^*\omega=\tau_D L(E_{-146965},1)\), using cusp Abel
limits or ordinary Mellin convergence. \(\tau_D\) is real
and \(\tau_D^2=D\); its common sign is irrelevant to the
following integrality. The image of C is an integral closed
elliptic period, so
\[
q_*=\sqrt D\,L(E_{-146965},1)/|\Omega^+_{E_{-1}}|\in\mathbb Z.
\]
This uses the primitive real period: the real component at
infinity on the split cubic traces one primitive cycle, not
the sum of periods over both real components.

## Exact interval and V13 convention

The literal primitive real period is the integral from 3 to
∞ of dx/sqrt(x(x+1)(x−3)): the two traversals with dx/(2y)
supply exactly that integral. Substituting x=−1+4/t² gives
\[
|\Omega^+_{E_{-1}}|
=\int_0^1 ((1-t²)(1-t²/4))^{-1/2}\,dt
=\frac{\pi}{2}\sum_{j\ge0}{\binom{2j}j^2\over64^j}.
\]
The exact script bounds π by alternating Machin sums, uses the
first 16 nonnegative terms, and bounds the series tail by
4^-16/(1−1/4). It bounds sqrt(D) by adjacent rationals with
denominator 10³⁰ and reads the binary endpoints of the previously
certified L interval exactly. The interval proved by Fraction
lies strictly between 204799/100 and 204801/100. Its only
integer is 2048; hence \(q_*=2^{11}\).

The complex isomorphism \(i_{\sqrt{-323}}\) from the original
E_-1 to E323 satisfies \(i^*\omega_{323}=\omega_{-1}/\sqrt{-323}\).
Consequently the primitive imaginary period absolute magnitude
on E323 is \(|\Omega^+_{E_{-1}}|/\sqrt{323}\).
V13 K14's real/imaginary primitive normalization on the same
fixed curve gives
\[
L_*(h_*)=\sqrt{455}L(E_{-146965},1)/|\Omega^-_{E_{323}}|
=q_*=2048.
\]
Thus ν₂=11 and no divisibility by 2¹², in this explicit
primitive period convention. Should a period generator be changed
by the fixed rational scalar discussed in K14, apply precisely its
valuation, not a new prime-dependent or relative conductor factor.
Using total real Néron volume instead of the primitive period would
introduce the explicit factor 2; we do not silently switch.

This is an actual same-data even genus-partner central value,
not the stationary rough companion k′ or the later independently
constructed final k of (3.9); it does not prove the simultaneous
address theorem. Its nonzero value gives the standard forward
rank-zero/finite Sha of this exact auxiliary companion, not any
analytic converse or assertion on rank for all selected n.
