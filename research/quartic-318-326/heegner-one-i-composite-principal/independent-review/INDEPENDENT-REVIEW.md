# Independent review of the exact factor-free faithful principal row

Bound to truncated author note hashes aec4e765 (principal norm) and
3e8208f9 (completed composite support), and exact completed manifest
896513232ef4ccbc27712c90c9e56ae61a90fe40e137c024344e573ea5da55c4.
The completed author packet replays to its exact JSON bytes.

For the same element a=W-169B, I separately recovered its 2768-digit
signed norm from the previously reviewed degree-14 line polynomial and
relative sextic in v. Multiplication by 169^2 B^2-13d v(v-13)(v+39)
in the relative sextic gives a 6-by-6 determinant in the line ring;
the 14-by-14 ordinary multiplication determinant gives the rational
norm. This independently reconstructs the signed integer from all 175
specified CRT primes, within the same certified archimedean bound,
and agrees at an extra prime. It uses neither the author's direct
degree-84 resultant recursion nor his multiplication-polynomial
construction of B. An independent sieve below 200000 confirms the
remaining integer C is coprime to all primes below that bound.
The exact decomposition is |Norm(a)|=3^29*13^333*5881*C.

I separately verified the exact selected coordinates at 5881 and
the full unfactored C by reducing the monic polynomial for v and
the radicand relation in their literal residue rings. Six successive
doublings starting from u=v/13 give B by half the sum, with every
point denominator invertible and W=169B. Factorization or squarefree
assumptions on C are unnecessary. At each rational p dividing C,
good reduction, p not dividing 2*13*d, makes the nonzero-torsion
sign quotient finite etale with distinct x-pair labels and unit
radicand, so the original integral v,W order is maximal locally.
This extends the residue map to O_F modulo C. The map is surjective
through the integer constants, so its kernel I_C has norm exactly C.
The principal ideal (a) is contained in I_C; equality of the p-parts
of their norms forces equality in each rational p-component of the
ideal. The residue ring Z/C is local at each p-component and gives
one residue-degree-one prime over p. That unramified prime has
trivial stabilizer under the actual relative group Delta. The same
argument gives a degree-one prime of multiplicity one at 5881.

At 3 the n=0 Tate coordinate expansions, with U=1 mod 3 choosing the
orbit representative, give dB=U^2(T+3T^2)/2 and y(P)=U^3(T/2+2T^2)
modulo terms of valuation at least 6. Since v(T)=2 and v(3)=13, the
linear term in y(P)-dB vanishes past depth 4, while the quadratic
coefficient is a unit. The one depth-4 point and eleven depth-2
points give coefficient 2 on e_lambda[w_3], equivalently coordinate
2/12=11 mod 13. All other 3-orbits and both 13-primes have nontrivial
stabilizers and vanish under this faithful projection. Hence the
exact class relation is 2e_lambda[w_3]+e_lambda[w_5881]+e_lambda[I_C]=0.

C^4=13 mod 53 precludes C being a thirteenth integer power. Since
at least one rational p exponent in C is then nonzero mod 13 and
its unique supported p-ideal is in a free orbit, the residual
projected divisor is not zero. This is not a statement about its
ideal class being nonzero. No generation, saturation, class-rank
bound, global S-powerclass, Selmer dimension, rational rank, or
point is claimed.

Independent replay (pass the four exact frozen JSON files in this
order): ACTUAL-DEGREE14-LINE-FIELD.json, EXACT-FIRST-PRINCIPAL-DIVISOR.json,
EXACT-COMPOSITE-SUPPORT.json, EXACT-POINT-FIELD-13.json.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
