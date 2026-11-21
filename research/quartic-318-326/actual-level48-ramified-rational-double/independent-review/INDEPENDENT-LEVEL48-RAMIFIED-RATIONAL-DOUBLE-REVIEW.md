# Independent cold review: the actual oriented level-48 trace is a rational double

**PASS** for the exact mathematical source and its finite parity replay, reviewed
21 November 2026. Author checksum list
`04ea85648b10394fa4298c048c4c89e8e698804d0389e4155d1635ee3696da02`;
paper `59feb8a9913e701fb1c82116c15908858712899c0bc53dfc603e100db36ea430`.
I checked the entire author list and compared the regenerated parity JSON
byte-for-byte. This is an exact mathematical source review, not a Lean build,
CM trace computation, or numerical detector certificate.

1. The ambient trace is the entire orbit for the same cyclic level ideal
   of norm 48. For the selected (nequiv23mod24), the two split primes
   allow that orientation, and the pinned modular-map identity is
   (phi w_{48}=T_3-phi). Ramified 17 and a distinct supported beta
   prime provide independent class-group elements of order two: a
   principal generator of norm one of the two primes or their product
   would be a rational integer (impossible by nonsquare norm) or have
   norm at least (n/4), larger than any of these. Thus (4mid h),
   and the raw trace itself, without multiplication by two, is anti-invariant.
2. Both (17) and (D/17) are fundamental discriminants, so the
   biquadratic discriminant of (K(sqrt {17})) is (D^2), proving the
   relevant genus extension unramified over (K). At a different
   ramified rational prime (pmid n), inertia and complex conjugation
   each act trivially on the real quadratic subfield. The class of the
   level ideal has character ((17/2)^4(17/3)=-1). Consequently the
   induced involution on the *characteristic-zero orbit indices* has no
   fixed class. Inertia fixes reduction, and each pair of reductions
   contributes (T_3); (h/2) is even. This yields reduction (O)
   at those primes without assuming that distinct indices stay distinct
   geometrically, and makes no analogous inertia claim at 17.
3. At such a place the nonzero formal point has anti-invariant parameter
   (z=sqrt D,u), of odd valuation in the ramified normalization.
   The integral-root terms (D(x-e)) have even valuation
   (1-v_{K_p}(z)). Independently evaluating the torsion Kummer images
   in order ((x_D+3n,x_D-n)) gives
   ((1,1),(3n,-n),(n,1),(3,-n)). Parity at the fresh (q_0)
   kills the torsion component of the rational trace class; parity at a
   distinct non-17 beta prime kills its marked component. The exact
   selected Selmer eight is used only to know these two components exhaust
   the group, not to assume rational realization of its marked class.
   The zero Kummer class therefore yields (P_Din 2E_n(mathbf Q)).

Given exact rational trace coordinates and nontorsion, the stated finite
two-saturation with torsion subtraction follows by strictly decreasing the
two-adic valuation of its nonzero free coefficient in rank one. A nonzero
order-three residue test can certify nontorsion under the pinned detector
conditions, but supplies neither those coordinates nor a marked half. No
small-prime phase is evaluated, no nonzero trace or rank is asserted, and no
unconditional quartic point is produced.

Signed: independent arithmetic and evidence reviewer.
