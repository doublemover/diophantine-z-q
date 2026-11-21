# Independent cold receipt: the two-coordinate Atkin field and exact eta phases

Signed: Vesper arithmetic lane, 2026-11-21 UTC.

Exact reviewed dependency is cbb41d8db7a9579e4a2f655a3427a28e7ca5c4243c8f6f89db1abbf15ece5f7d.
The exact checker output and all manifest members were replayed byte-for-byte. No dependency was edited.

I independently checked:
1. For each odd \(\ell\), the determinant-\(\ell\) representative and the two paired matrices are exactly in \(\Gamma_0(4)\). The lower factors are multiples of the same upper-half-plane complex number by positive real constants, hence there is no unaccounted square-root sign. The actual Savitt Theorem 4.1 formula gives the two written exponents. Each character has enough negative primes off \(\ell\) for the needed zero weight and divisibility by 24; the Jacobi product is a square. The level \(N\) Fricke formula and odd local signs correctly recover \(W_2\).
2. The eta function has trivial \(\Gamma_0(N)\) character by exact Savitt 1.1 (integer weight zero, both cusp congruences, divisor product 1). Rational q coefficients specify the rational normalization visibly. Integrality of \(u,u^{-1}\) over the normalized model via \(U=u^{24}\) and the algebraic unit \(U\) suffices away from cusps. At the rational cusps the normalized Laurent coefficient is a unit, and the tame quotient leaves the width-one parameter unchanged.
3. The restriction of the single cusp valuation has ramification dividing \(m\) and \(3m-1\). Every point over it is a pole of the first coordinate, so there is only one, with residue degree one. The degree formula for the finite morphism between the smooth normalized curves (free over a DVR) then gives field degree one; separability is not required. The coefficients 4 or 96 in the cancellation are units at the asserted good primes \(p>3\).
4. The independently authored 2400-slice 0feb0ab7 computes the **discriminant-power** and \(c_4\) readings, not q-normalized eta roots. Its finite collisions are compatible with birationality and mean normalization cannot be discarded. No exact eta \(\,24\)th root at the tested marks, quotient equation, \(R\), or actual mod-13 cubic character was produced by this review.

Primary check: [Savitt, Theorems 1.1 and 4.1](https://arxiv.org/pdf/2507.16225). Scope remains the original fixed lower level; there is no new weight-two readout, nonzero trace or point.

