# Independent actual metric-producer review

## Result and scope

Accepted as a mathematical derivation conditional on the named branch model, regular semistable maximal stack, and application of Yuan's Kodaira–Spencer theorem. This is not a Lean proof of complex differential geometry or the Shimura model. I independently recomputed the formulas rather than inheriting the producer's conclusion. I also read the original Yuan PDF text at printed pages 2–3 and Gaudron–Rémond 2014, section 2.3, printed pages 351–352.

## Concrete checks

1. At a finite branch, `t-a_i=z^2` cancels the factor `|z|^2` in the metric denominator against `|dt|^2`. The exceptional absolute value becomes `|z|^2`, which is smooth. At infinity `t=z^-2` gives coefficient `4(|z|^2+sum |1-a_i*z^2|)/product |1-a_i*z^2|`, smooth and positive with value 16. Thus the maximum-principle argument really occurs on the compact curve without boundary or a singular curvature contribution.
2. With `U=1+sum r_i`, curvature has numerator `U sum(1/r_i)-|grad U|^2`. The two estimates `|grad U|^2<=16` and `(sum r_i)(sum 1/r_i)>=16` leave the positive term `sum 1/r_i`. This gives exactly the finite distance quotient used by the separate checked constants. The interior `1/(16 U^3)` and exterior `1/1372` bounds have the stated direction.
3. For `f=rho/(Cmet*h)`, at a maximum above 1, `Delta log f >= 2h(f-1)>0`, a contradiction. Thus `rho/Cmet<=h`; no reversed comparison is hidden.
4. Yuan explicitly uses `||d tau||=2 Im(tau)` and a squared Hodge norm with factor `(2pi)^-2`. Therefore the quadratic-differential norm is `4|f(t)|/h_t`. This verifies the factor four in both q0/q1 estimates, not merely a convention supplied by the manuscript.
5. The actual sections have no common generic zero: q0 is nonzero at finite branches, while at infinity q0 has order two and q1 is nonzero. Their quotient is exactly t.
6. For a vertical generic point of the retained semistable regular model, `v(du)>=v(u)` follows from writing `u=p^r*v` and relative differentiation killing p. If `v(t)>=0`, at most one contact valuation exceeds delta, and `2 max r_i-sum r_i>=-2delta`; if `v(t)<0`, both q0 and q1 are already integral. The maxima of the pairwise differences are exactly `2^10*3^2*5^3*7^4`. Normality/reflexivity on an etale atlas justifies extension from codimension one. These conclusions use, rather than construct, the stated model.
7. Yuan's Theorem 1.1 gives image `d_B*omega^2` with the induced metric. The sublattice has degree `h(omega^2)-log d_B`, so solving gives the positive `+log210` term. GR2014 explicitly states `h_original=h_shifted-(g/2)log pi`, agreeing with `+2log pi` after the dimension-two Hodge square. The section height bound then adds `2logJ+log(4Cmet)+log32`, all with the stated signs. Adding a dimension-linear correction preserves the equal-dimension isogeny comparison; using the larger shifted height in an upper-bound maximum is monotonicity, not identification of normalizations.

## Remaining boundary

This review does not prove the existence/identification of the five-branch Shimura model, its proper regular semistable integral stack, the required actual fiber and ramification/level controls, the modular Jacobian source map, or the full `FiveContact49Height` proposition. The metric and finite-extension calculation has no additional unexplained curvature or Petersson-normalization input once those named geometric inputs are supplied.
