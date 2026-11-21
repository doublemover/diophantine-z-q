# Independent review: two denominator constraints for literal slot 190

Reviewed exact notes and export manifests:
- Universal square-contact 2399: note 946ff901, manifest aa75805066e0d709ad4edfcd5c34f375972b17b43e0e996d61728b0d6c6f2d22.
- Pythagorean square-contact 407: note 26c35716, manifest 7b87a867d0476b91ce5223354d3838bdf5f7f042417d3389e82a9eac0fe4af90.

Both author checker outputs independently replay byte-for-byte. I separately enumerated the square residues modulo 2399, the simultaneous square T and T+1 rows at 11 and 37, and the displayed actual p=35533 witness modulo p^2. For the 2399 half-point I separately recomputed first returns and midpoint coordinates using the least-significant-bit lifted group law modulo 2399^2: (sqrt2, order, midpoint) = (49,300,(46,0)) and (2350,80,(2347,0)), as in the exact author JSON.

For a primitive square t=r^2/d^2>2 and d a 2399-unit, the four linear factors are units on every T residue square. Thus v_2399(F)=2v_2399(r)-1. If negative, every weighted nonzero leaf has odd valuation even when Delta=t-1 is a nonunit, because the Delta exponents in all weights are even. Each parity-minimum chain ends with valuation at most zero, and the reciprocal trace either vanishes (then b=0) or yields v_2399(b)<0 odd. If positive, Delta is a unit and the original early-eight reduction applies. The opposite half-order cannot be T0 because each displayed midpoint has nonzero x, and the two simultaneous h constraints in the two orientations have cross gcds 10 and 20. Neither is possible. Therefore 2399 divides d for the unscaled slot, regardless of guarded h. Saturation removes this negative odd obstruction, since G3 has depth one and cancels the fixed denominator's depth one.

For the Pythagorean subfamily r^2+d^2=s^2, odd G1 divisors split in Q(sqrt(2)), from simultaneous square roots of -2 and -1, without imposing their correct elliptic orientation. If d is an 11- or 37-unit, the simultaneous residue rows leave all linear factors nonvanishing except G2 at T=-1 (at 37); G0 and G2 have even depth. The fixed denominator has depth one. Positive odd F arises only at T=0 or -1, so Delta is a unit and inert early-eight applies; negative odd F uses the same Delta-integral parity argument as above. Thus both 11 and 37 divide d. Saturation gives depth one exactly for G4 and cancels that fixed factor. Independent arithmetic confirmed the displayed saturated Pythagorean example still fails at inert 35533, with G4 the unique simple contact.

After rational Pythagorean parametrization, the even reciprocal quartics H3 and H4 remain irreducible over Q(sqrt(2)): the three required quadratic classes for each are not rational squares or twice rational squares. They are distinct invariant polynomial places, so neither their product nor the remaining full generic contact has a norm identity. This is a rational-function field obstruction only; it does not exclude every specialization.

Together the exact necessary divisors are 2399 for the square-contact family and 2399*407 for its Pythagorean subfamily. No condition is claimed sufficient, no supply for other scales or all linked poles is shown, and no actual rational PointPair or new Lean theorem is produced.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
