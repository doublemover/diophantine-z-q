# Independent exact review: derivative of the actual residual Gaussian scalar

**PASS, classical proof with its stated inputs.** Author list
`1fc60f085f5ed431e07a3cce0a476350f96c40af3f49b98487e813cfab8bc9f9`;
exact paper
`629620bbc565ab6dd0aabddc439b4ce69145bd89896d43ee8fe74b5c55827a43`.
All author files rehashed and the finite control output reproduced
byte-for-byte. Earlier staged native source was read only for the
actual two-germ seam and does not acquire compilation evidence here.

On the actual projective chart [-s:1:-w], the curve equation is
w+s*w^2=s^3. I checked the divided difference including the tangent,
the chord cubic, and the sign after reflecting the third point.
The kernel chart remains valid at all intersections because
1-lambda^2 is a unit, and the true parameter is additive to first
order. The chosen quarter-turn multiplies it by i, so the selected
Gaussian scalar kills that first-order term when a+b*i vanishes.

At an actual finite test point Q with both y and B(x) nonzero, the
mixed secant gives x+2*y*t modulo t squared for the same origin
parameter. The coefficient is nonzero, giving a faithful actual
function-field substitution after base extension to the algebraic
closure. The rational scalar abscissa evaluates integrally because
its literal denominator has nonzero residue. If the scalar of the
constant Q were infinity, the scalar of the translated point would
reduce to infinity as well, contradicting the finite integral
abscissa. The second true mixed germ, at that finite scalar of Q
and in the same t, is stationary to first order; no independent
formal parameter is substituted. The two quotient jets give the
cross derivative. Multiplication by the two exceptional polynomials
before cancellation proves the identity over the original field.

I checked the optional final step separately. It explicitly needs
the *additional* coprime degree bound with numerator larger than
denominator at a prime residue field of characteristic p >= 5.
The zero derivative then gives c*X^p+d, and the anti-invariant
ordinate with the three simple branch factors forces d=0 and c=+-1.
The four allowed unit maps after positive coordinate Frobenius
follow in the actual function field. This step fixes neither the
primary unit at the chosen place nor the characteristic-zero
degree bound or its no-degree-rise input.

This is paper evidence and bounded source arithmetic, not a new
Lean check, source of primes, or theorem about 318/326 rational
points. No local Lean was invoked.

Signed: independent paper and exact-byte reviewer, 2026-11-21.
