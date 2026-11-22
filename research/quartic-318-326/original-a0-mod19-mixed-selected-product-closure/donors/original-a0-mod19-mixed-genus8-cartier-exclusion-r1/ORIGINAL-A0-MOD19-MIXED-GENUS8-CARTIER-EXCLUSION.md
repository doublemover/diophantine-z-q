# A mod-19 certificate excluding the actual ordinary target from the mixed trace base

Use the exact mixed primary-1 × alternate-1 transition and its geometric genus-15 trace base from the separate frozen split proof. That proof identifies the two factors on an explicitly fixed model over F₁₉. The genus-seven factor is covered by Fermat degree 16, which excludes the actual ordinary elliptic targets by the preceding exact Jacobi-sum argument. This note certifies the different genus-eight factor

    C_8: W²=(x−1)(x^16+1)

against those same target elliptic curves. There are no uncomputed parameter coefficients in this fixed model. No other mixed boundary or local resolution is addressed.

## 1. Exact modular characteristic polynomial

The degree-17 squarefree polynomial F=(x−1)(x^16+1) defines a smooth projective hyperelliptic curve of genus 8 over the prime field. Form its Hasse–Witt matrix H with (i,j) entry [x^(19i−j)] F^9 for i,j=1,…,8 (a transpose convention gives the same characteristic polynomial). The index formula and the prime-field characteristic polynomial congruence are [Manin, The Hasse–Witt matrix of an algebraic curve, Thm. 1](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=3370&wshow=paper), with the explicit hyperelliptic matrix/congruence also in [Bostan–Gaudry–Schost, §2, Def. 1 and Thm. 2](https://cs.uwaterloo.ca/~eschost/publications/cartier.pdf). In characteristic-polynomial convention the degree-sixteen Frobenius polynomial of Jac(C_8) reduces to T^8 det(TI−H), not just det(TI−H).

The exact eight-row replay uses F^9=(x−1)^9(x^16+1)^9 and Newton identities (integers 1,…,8 invertible modulo 19). It gives

    det(TI−H) =
      (T^4−T^3−6T²+6T−8)(T^4−T^3−4T²+6T−8)  over F₁₉.

Both quartics are irreducible: the replay checks that T^(19^4) reduces to T, and gcd with T^(19²)−T is 1. In each quartic field the element λ/4, where λ is the polynomial variable's root, has exact order 16290 and 8145 respectively. The finite group order is 19^4−1=2^4·3²·5·181; prime-by-prime power divisions with witnesses verify the two exact orders. The totient of both orders is 4320.

## 2. Geometry over any constant extension, not just an F₁₉ test

The actual three elliptic targets have trace ±4 at 19. Up to sign the roots are a=2+sqrt(−15), abar=2−sqrt(−15); at either place selecting the unit target root it reduces to 4 after choosing the plus trace pair. The sign change for a twist can be absorbed into a root of unity. Their distinct 19-adic valuations 0 and 1 follow from X²−4X+19 and its two simple roots 0,4 modulo 19.

Suppose a required geometric elliptic quotient of Jac(C_8) exists. The quotient and its isogeny to a fixed target descend to some finite extension of F₁₉, and Frobenius on that extension acts by powers of the original eigenvalues. Therefore for some degree-at-most-16 Frobenius eigenvalue γ of Jac(C_8), the ratio γ/a (or its conjugate-target variant) is a root of unity up to sign. More explicitly one may choose a 19-adic embedding where a chosen target eigenvalue is a unit; the matching exact equation of powers forces γ to be a unit there too. Choose coherent sign so the target root reduces to 4. The field Q(γ,a) has degree at most 2·16=32, so the exact root of unity can have order m only if φ(m)≤32. Its reduction in characteristic 19 has order dividing m, and thus also totient ≤32.

On the other hand the unit root γ has nonzero reduction λ, necessarily a root of one of the two explicit quartics by the congruence. The reduced ratio λ/4 has totient 4320, a contradiction. This proves absence of the required **geometric** elliptic quotient, not merely lack of one over F₁₉. The actual trace model may require finite constant extension to identify it with the fixed displayed model. The calculation is deliberately on the latter over its prime field: H is its prime-field Frobenius matrix. Over F_(19^f) the semilinear rule gives H H^(19)…H^(19^(f−1))=H^f in this fixed basis, equivalently the exact eigenvalues are raised to powers. No linearity assertion is made in an arbitrary basis of the actual rescaled chart. If such a modular screen failed, it would not prove any quotient.

Together with the checked genus-7 Fermat factor this excludes a required geometric ordinary quotient of the actual C_15 trace base. On the selected mixed torus its simple-cancellation generic balanced contact component is a rational conic over the trace function field by the exact contact formula (both folds are units there). Any elliptic map already known to factor through this base must therefore be constant. This note does not assemble a proper graph near omitted axes, infinity, other pole intersections, or other valuations.

Exact binding: mixed split manifest b6cac3561eaf495332b35cd62ba95b0b6deadfd038a3ede16951f61d4a980d0f/paper f74ed32e145d872927af0fdf8dcfd9986798c752dfabd7cd00499e97e4a031bf; Fermat exact quotient manifest 5dd7a58c5968b03b49cb0c57a16c69f8d6dfb08caaa6bf4e969f0ca5805d230b; actual good-target count list e9a3423e5bf681944b8a70529990763bfce3f8e2db92fe8b1b5bdb64fb4b9e7f. The replay uses the standard library and no further finite fields or division-point search.

    sha256sum -c SHA256SUMS
    python3 -B replay_mixed_genus8_cartier19.py | cmp - EXACT-MIXED-GENUS8-CARTIER19.json
